/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 34 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile017Terms2
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨17,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (987/128)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (987/128))
  have he : value ((3/4), (987/128))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-1116391677/536870912), (-22955803857/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-23816355775/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-921620800226043/9007199254740992), (-646734644579527/9007199254740992)), (24913/35184372088832), by norm_num⟩
  | 1 => ⟨((4873801111/17179869184), (6840244987/34359738368)), (137/68719476736), by norm_num⟩
  | 2 => ⟨((-13513045995/34359738368), (-4741296527/17179869184)), (97/34359738368), by norm_num⟩
  | 3 => ⟨((6244353155/17179869184), (8763776853/34359738368)), (91/34359738368), by norm_num⟩
  | 4 => ⟨((-541031973/2147483648), (-6074587217/34359738368)), (129/68719476736), by norm_num⟩
  | 5 => ⟨((9600378539/68719476736), (1684233201/17179869184)), (73/68719476736), by norm_num⟩
  | 6 => ⟨((-17745267511/274877906944), (-12452495943/274877906944)), (137/274877906944), by norm_num⟩
  | 7 => ⟨((54911081/2147483648), (616529461/34359738368)), (55/274877906944), by norm_num⟩
  | 8 => ⟨((-4871867005/549755813888), (-3418765261/549755813888)), (155/2199023255552), by norm_num⟩
  | 9 => ⟨((12006829791/4398046511104), (8425626673/4398046511104)), (97/4398046511104), by norm_num⟩
  | 10 => ⟨((-3329000087/4398046511104), (-9344318997/17592186044416)), (55/8796093022208), by norm_num⟩
  | 11 => ⟨((13425379051/70368744177664), (9421073989/70368744177664)), (113/70368744177664), by norm_num⟩
  | 12 => ⟨((-6203842425/140737488355328), (-8706921165/281474976710656)), (53/140737488355328), by norm_num⟩
  | _ => zero

def term16ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581267062326325/10141204801825835211973625643008), (-3295219856425/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889376755547673/316912650057057350374175801344), (-1949845171531/316912650057057350374175801344)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944862138641235/19807040628566084398385987584), (-4386335839245/39614081257132168796771975168)), (3257/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889497726218575/2475880078570760549798248448), (-4659491177041/2475880078570760549798248448)), (3461/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((442790846084529/38685626227668133590597632), (-4658376804645/154742504910672534362390528)), (1731/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549527200813879/9671406556917033397649408), (-2183022213451/4835703278458516698824704)), (3247/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258765109629801/604462909807314587353088), (-3819105263123/604462909807314587353088)), (1421/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((943876280814481/37778931862957161709568), (-6203827244427/75557863725914323419136)), (1155/18889465931478580854784), by norm_num⟩
  | 10 => ⟨((1297508812729897/4722366482869645213696), (-290683089861/295147905179352825856)), (3467/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405351078631559/147573952589676412928), (-6391874725079/590295810358705651712)), (4769/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911708683331195/36893488147419103232), (-3992557522365/36893488147419103232)), (2983/36893488147419103232), by norm_num⟩
  | 7 => ⟨((7119488426015/36028797018963968), (-2244188848369/2305843009213693952)), (6717/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593833234936805/1152921504606846976), (-2242158826131/288230376151711744)), (6725/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597221189556347/72057594037927936), (-3919212942289/72057594037927936)), (1473/36028797018963968), by norm_num⟩
  | 4 => ⟨((186427522565851/4503599627370496), (-5869695779789/18014398509481984)), (8855/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488969335762753/9007199254740992), (-7321167724121/4503599627370496)), (11097/9007199254740992), by norm_num⟩
  | 2 => ⟨((278415147176663/562949953421312), (-14594536971413/2251799813685248)), (11141/2251799813685248), by norm_num⟩
  | 1 => ⟨((553759672455475/562949953421312), (-5443127753503/281474976710656)), (4205/281474976710656), by norm_num⟩
  | 0 => ⟨((1089054598902663/1125899906842624), (-21534529008099/562949953421312)), (34079/1125899906842624), by norm_num⟩
  | _ => zero

def term16ValueSquares : ℕ → Disk
  | 0 => ⟨((1089054598902663/1125899906842624), (-21534529008099/562949953421312)), (130001072410201671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1051767540290027/1125899906842624), (-41659614160979/562949953421312)), (8567/140737488355328), by norm_num⟩
  | 2 => ⟨((976350436054545/1125899906842624), (-155666519374351/1125899906842624)), (8637/70368744177664), by norm_num⟩
  | 3 => ⟨((1650285434937215/2251799813685248), (-134989862905713/562949953421312)), (138943/562949953421312), by norm_num⟩
  | 4 => ⟨((269993561660027/562949953421312), (-791444437515557/2251799813685248)), (135145/281474976710656), by norm_num⟩
  | 5 => ⟨((239790443382205/2251799813685248), (-759161276210001/2251799813685248)), (3594109/4503599627370496), by norm_num⟩
  | 6 => ⟨((-921620800226043/9007199254740992), (-646734644579527/9007199254740992)), (24913/35184372088832), by norm_num⟩
  | _ => zero

def term16Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1116391677/536870912), (-22955803857/1073741824)), (1/536870912), by norm_num⟩, -3, term16ValuePoly, term16ValueSquares⟩

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
  | 0 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-570401187/268435456), (-11728874407/536870912)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-24337117311/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-532326806044849/4503599627370496), (-9677036849853/562949953421312)), (1415205/2251799813685248), by norm_num⟩
  | 1 => ⟨((23013235631/68719476736), (1673407589/34359738368)), (31/17179869184), by norm_num⟩
  | 2 => ⟨((-8150175785/17179869184), (-592640089/8589934592)), (45/17179869184), by norm_num⟩
  | 3 => ⟨((15394124527/34359738368), (2238767745/34359738368)), (87/34359738368), by norm_num⟩
  | 4 => ⟨((-21807419515/68719476736), (-3171453325/68719476736)), (125/68719476736), by norm_num⟩
  | 5 => ⟨((6178507197/34359738368), (224635097/8589934592)), (9/8589934592), by norm_num⟩
  | 6 => ⟨((-5835009679/68719476736), (-3394342157/274877906944)), (69/137438953472), by norm_num⟩
  | 7 => ⟨((9446758449/274877906944), (2747684427/549755813888)), (57/274877906944), by norm_num⟩
  | 8 => ⟨((-1672792631/137438953472), (-973097023/549755813888)), (163/2199023255552), by norm_num⟩
  | 9 => ⟨((8425561607/2199023255552), (2450659085/4398046511104)), (13/549755813888), by norm_num⟩
  | 10 => ⟨((-19097130861/17592186044416), (-2777296009/17592186044416)), (15/2199023255552), by norm_num⟩
  | 11 => ⟨((9837499271/35184372088832), (1430667657/35184372088832)), (63/35184372088832), by norm_num⟩
  | 12 => ⟨((-9290578069/140737488355328), (-1351128899/140737488355328)), (121/281474976710656), by norm_num⟩
  | _ => zero

def term17ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581207834572315/10141204801825835211973625643008), (-3904155202263/10141204801825835211973625643008)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889340067341787/316912650057057350374175801344), (-4619981219753/633825300114114700748351602688)), (2897/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((944820779699615/19807040628566084398385987584), (-2598241583845/19807040628566084398385987584)), (3259/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1889409615142217/2475880078570760549798248448), (-2760031527353/1237940039285380274899124224)), (433/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((1771075022223791/154742504910672534362390528), (-5518712707351/154742504910672534362390528)), (3465/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549444094795913/9671406556917033397649408), (-2586179290281/4835703278458516698824704)), (1625/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258692125544121/604462909807314587353088), (-4524379356523/604462909807314587353088)), (2845/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((471908365899571/18889465931478580854784), (-3674713668465/37778931862957161709568)), (4625/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297419053135175/4722366482869645213696), (-5509717910817/4722366482869645213696)), (3471/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810640093662957/295147905179352825856), (-7572039890183/590295810358705651712)), (4775/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911630573764025/36893488147419103232), (-4729658888633/36893488147419103232)), (2987/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1822411835289615/9223372036854775808), (-2658463237597/2305843009213693952)), (841/1152921504606846976), by norm_num⟩
  | 6 => ⟨((398413554442287/288230376151711744), (-10624006624145/1152921504606846976)), (6737/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194283701794263/144115188075855872), (-9284932967329/144115188075855872)), (5905/144115188075855872), by norm_num⟩
  | 4 => ⟨((372794525626829/9007199254740992), (-6952632274791/18014398509481984)), (8877/36028797018963968), by norm_num⟩
  | 3 => ⟨((744329828936845/4503599627370496), (-17342868908607/9007199254740992)), (11129/9007199254740992), by norm_num⟩
  | 2 => ⟨((1113340346605927/2251799813685248), (-17284850082631/2251799813685248)), (5591/1125899906842624), by norm_num⟩
  | 1 => ⟨((1107012768036027/1125899906842624), (-25782400095177/1125899906842624)), (16901/1125899906842624), by norm_num⟩
  | 0 => ⟨((543968884065761/562949953421312), (-50986340971749/1125899906842624)), (17161/562949953421312), by norm_num⟩
  | _ => zero

def term17ValueSquares : ℕ → Disk
  | 0 => ⟨((543968884065761/562949953421312), (-50986340971749/1125899906842624)), (65464021922874273/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((262236672457241/281474976710656), (-98534453488947/1125899906842624)), (69439/1125899906842624), by norm_num⟩
  | 2 => ⟨((484314863581925/562949953421312), (-183599604535333/1125899906842624)), (141541/1125899906842624), by norm_num⟩
  | 3 => ⟨((1606776460434361/2251799813685248), (-631814724444447/2251799813685248)), (579405/2251799813685248), by norm_num⟩
  | 4 => ⟨((969242796147701/2251799813685248), (-450832716311371/1125899906842624)), (576007/1125899906842624), by norm_num⟩
  | 5 => ⟨((56146663095483/2251799813685248), (-1552416373415953/4503599627370496)), (3828605/4503599627370496), by norm_num⟩
  | 6 => ⟨((-532326806044849/4503599627370496), (-9677036849853/562949953421312)), (1415205/2251799813685248), by norm_num⟩
  | _ => zero

def term17Value : CertifiedScalarExp.Data :=
  ⟨⟨((-570401187/268435456), (-11728874407/536870912)), (1/536870912), by norm_num⟩, -3, term17ValuePoly, term17ValueSquares⟩

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
  | 0 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2327634783/1073741824), (-5982748777/268435456)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-24828104347/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-492892196788277/4503599627370496), (150488254949275/4503599627370496)), (2811115/4503599627370496), by norm_num⟩
  | 1 => ⟨((21738306965/68719476736), (-6637069733/68719476736)), (63/34359738368), by norm_num⟩
  | 2 => ⟨((-15707947129/34359738368), (299743733/2147483648)), (93/34359738368), by norm_num⟩
  | 3 => ⟨((15133935585/34359738368), (-577580547/4294967296)), (23/8589934592), by norm_num⟩
  | 4 => ⟨((-1366959375/4294967296), (1669422501/17179869184)), (135/68719476736), by norm_num⟩
  | 5 => ⟨((25286532939/137438953472), (-3860201319/68719476736)), (79/68719476736), by norm_num⟩
  | 6 => ⟨((-12181246777/137438953472), (7438277915/274877906944)), (77/137438953472), by norm_num⟩
  | 7 => ⟨((20119046663/549755813888), (-1535670601/137438953472)), (129/549755813888), by norm_num⟩
  | 8 => ⟨((-3634470267/274877906944), (4438658935/1099511627776)), (95/1099511627776), by norm_num⟩
  | 9 => ⟨((4668875651/1099511627776), (-5701944191/4398046511104)), (31/1099511627776), by norm_num⟩
  | 10 => ⟨((-21591658117/17592186044416), (3296147691/8796093022208)), (73/8796093022208), by norm_num⟩
  | 11 => ⟨((22693788665/70368744177664), (-1732198581/17592186044416)), (39/17592186044416), by norm_num⟩
  | 12 => ⟨((-21864495279/281474976710656), (6675597143/281474976710656)), (153/281474976710656), by norm_num⟩
  | _ => zero

def term18ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((395287998290011/2535301200456458802993406410752), (1853137832879/5070602400912917605986812821504)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((889307593050709/316912650057057350374175801344), (1096377548289/158456325028528675187087900672)), (181/39614081257132168796771975168), by norm_num⟩
  | 16 => ⟨((472392142741669/9903520314283042199192993792), (2466369711387/19807040628566084398385987584)), (1629/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889332165292941/2475880078570760549798248448), (1309968434447/618970019642690137449562112)), (3463/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770997685227567/154742504910672534362390528), (5238566671273/154742504910672534362390528)), (433/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((1549371711208231/9671406556917033397649408), (2454883847957/4835703278458516698824704)), (3249/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314657227420925/151115727451828646838272), (2147329199871/302231454903657293676544)), (711/151115727451828646838272), by norm_num⟩
  | 11 => ⟨((1887530962266971/75557863725914323419136), (3488108624903/37778931862957161709568)), (4623/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297342373379957/4722366482869645213696), (5229886096011/4722366482869645213696)), (3469/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((405293767822249/147573952589676412928), (1796848602605/147573952589676412928)), (4773/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823130229951303/73786976294838206464), (8978696124559/73786976294838206464)), (1493/18446744073709551616), by norm_num⟩
  | 7 => ⟨((227783151096493/1152921504606846976), (10093408721071/9223372036854775808)), (6725/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796754204900223/576460752303423488), (5041941015751/576460752303423488)), (6733/1152921504606846976), by norm_num⟩
  | 5 => ⟨((149269629889173/18014398509481984), (4406342266307/72057594037927936)), (5901/144115188075855872), by norm_num⟩
  | 4 => ⟨((1490989943130531/36028797018963968), (13197615537133/36028797018963968)), (8869/36028797018963968), by norm_num⟩
  | 3 => ⟨((1488427660420025/9007199254740992), (16459579548013/9007199254740992)), (11119/9007199254740992), by norm_num⟩
  | 2 => ⟨((278278283521769/562949953421312), (8201739792655/1125899906842624)), (349/70368744177664), by norm_num⟩
  | 1 => ⟨((1106683849611783/1125899906842624), (24465179733945/1125899906842624)), (16875/1125899906842624), by norm_num⟩
  | 0 => ⟨((543663580498315/562949953421312), (48371468803255/1125899906842624)), (8561/281474976710656), by norm_num⟩
  | _ => zero

def term18ValueSquares : ℕ → Disk
  | 0 => ⟨((543663580498315/562949953421312), (48371468803255/1125899906842624)), (32657624364757449/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((261999434602435/281474976710656), (46714287413501/562949953421312)), (69085/1125899906842624), by norm_num⟩
  | 2 => ⟨((241933220372409/281474976710656), (86964155984453/562949953421312)), (35019/281474976710656), by norm_num⟩
  | 3 => ⟨((804916908425107/1125899906842624), (597979076084335/2251799813685248)), (142037/562949953421312), by norm_num⟩
  | 4 => ⟨((496044525997131/1125899906842624), (106875279565145/281474976710656)), (278525/562949953421312), by norm_num⟩
  | 5 => ⟨((112448656000325/2251799813685248), (753387004589047/2251799813685248)), (3655467/4503599627370496), by norm_num⟩
  | 6 => ⟨((-492892196788277/4503599627370496), (150488254949275/4503599627370496)), (2811115/4503599627370496), by norm_num⟩
  | _ => zero

def term18Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2327634783/1073741824), (-5982748777/268435456)), (1/536870912), by norm_num⟩, -4, term18ValuePoly, term18ValueSquares⟩

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
  | 0 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-592793865/268435456), (-24378647699/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-25292538241/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-748495168687097/9007199254740992), (647576868265937/9007199254740992)), (5638357/9007199254740992), by norm_num⟩
  | 1 => ⟨((8407205011/34359738368), (-14547352393/68719476736)), (129/68719476736), by norm_num⟩
  | 2 => ⟨((-6188625535/17179869184), (10708447857/34359738368)), (97/34359738368), by norm_num⟩
  | 3 => ⟨((1518502521/4294967296), (-10510123759/34359738368)), (97/34359738368), by norm_num⟩
  | 4 => ⟨((-17884552051/68719476736), (3868302259/17179869184)), (145/68719476736), by norm_num⟩
  | 5 => ⟨((10531994437/68719476736), (-2277995991/17179869184)), (87/68719476736), by norm_num⟩
  | 6 => ⟨((-2584234579/34359738368), (1117903365/17179869184)), (87/137438953472), by norm_num⟩
  | 7 => ⟨((8696138315/274877906944), (-15047306253/549755813888)), (37/137438953472), by norm_num⟩
  | 8 => ⟨((-12802624311/1099511627776), (5538234383/549755813888)), (111/1099511627776), by norm_num⟩
  | 9 => ⟨((8377010235/2199023255552), (-3623776265/1099511627776)), (37/1099511627776), by norm_num⟩
  | 10 => ⟨((-4933119093/4398046511104), (8535990469/8796093022208)), (89/8796093022208), by norm_num⟩
  | 11 => ⟨((10563831379/35184372088832), (-4569764193/17592186044416)), (97/35184372088832), by norm_num⟩
  | 12 => ⟨((-10368185627/140737488355328), (4485130605/70368744177664)), (97/140737488355328), by norm_num⟩
  | _ => zero

def term19ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790549585858251/5070602400912917605986812821504), (3163205192563/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((444638870799071/158456325028528675187087900672), (1871331404861/316912650057057350374175801344)), (1447/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((236187697064197/4951760157141521099596496896), (526208662055/4951760157141521099596496896)), (407/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889261205850061/2475880078570760549798248448), (2235882177157/1237940039285380274899124224)), (865/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1770926975551057/154742504910672534362390528), (2235314551283/77371252455336267181195264)), (3461/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((387326421525167/2417851639229258349412352), (4190008824023/9671406556917033397649408)), (1623/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1258571402746019/604462909807314587353088), (1832526018537/302231454903657293676544)), (2841/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887438010038995/75557863725914323419136), (5953449488769/75557863725914323419136)), (4619/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297273093298455/4722366482869645213696), (4463110140055/4722366482869645213696)), (1733/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621080515844999/590295810358705651712), (766695619341/73786976294838206464)), (149/18446744073709551616), by norm_num⟩
  | 8 => ⟨((911506545688061/36893488147419103232), (3831070442651/36893488147419103232)), (1491/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822134877436923/9223372036854775808), (8613290574047/9223372036854775808)), (6715/9223372036854775808), by norm_num⟩
  | 6 => ⟨((398344971830035/288230376151711744), (8605022863099/1152921504606846976)), (3361/576460752303423488), by norm_num⟩
  | 5 => ⟨((1194046612648053/144115188075855872), (7520100283327/144115188075855872)), (2945/72057594037927936), by norm_num⟩
  | 4 => ⟨((93176772138105/2251799813685248), (11261577120073/36028797018963968)), (4425/18014398509481984), by norm_num⟩
  | 3 => ⟨((744116369614817/4503599627370496), (14044504446711/9007199254740992)), (5545/4503599627370496), by norm_num⟩
  | 2 => ⟨((1112928762599939/2251799813685248), (6997938360601/1125899906842624)), (11133/2251799813685248), by norm_num⟩
  | 1 => ⟨((553216749916021/562949953421312), (20872500430309/1125899906842624)), (16803/1125899906842624), by norm_num⟩
  | 0 => ⟨((543465146303153/562949953421312), (20630635888475/562949953421312)), (34027/1125899906842624), by norm_num⟩
  | _ => zero

def term19ValueSquares : ℕ → Disk
  | 0 => ⟨((543465146303153/562949953421312), (20630635888475/562949953421312)), (129802708152389171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((130974672045323/140737488355328), (79666275720009/1125899906842624)), (34097/562949953421312), by norm_num⟩
  | 2 => ⟨((1938951446378955/2251799813685248), (148279814531811/1125899906842624)), (68289/562949953421312), by norm_num⟩
  | 3 => ⟨((1630511324990231/2251799813685248), (255357833416577/1125899906842624)), (542361/2251799813685248), by norm_num⟩
  | 4 => ⟨((133101123932087/281474976710656), (739610753638505/2251799813685248)), (1031459/2251799813685248), by norm_num⟩
  | 5 => ⟨((32573617214055/281474976710656), (1398959491631657/4503599627370496)), (1653065/2251799813685248), by norm_num⟩
  | 6 => ⟨((-748495168687097/9007199254740992), (647576868265937/9007199254740992)), (5638357/9007199254740992), by norm_num⟩
  | _ => zero

def term19Value : CertifiedScalarExp.Data :=
  ⟨⟨((-592793865/268435456), (-24378647699/1073741824)), (1/536870912), by norm_num⟩, -4, term19ValuePoly, term19ValueSquares⟩

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
  | 0 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2412482277/1073741824), (-775104169/33554432)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-25733144285/8589934592), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-212277327831609/4503599627370496), (213132921597695/2251799813685248)), (5302099/9007199254740992), by norm_num⟩
  | 1 => ⟨((9703461333/68719476736), (-9742571591/34359738368)), (123/68719476736), by norm_num⟩
  | 2 => ⟨((-3633621535/17179869184), (14593068071/34359738368)), (47/17179869184), by norm_num⟩
  | 3 => ⟨((1814226217/8589934592), (-7286154165/17179869184)), (3/1073741824), by norm_num⟩
  | 4 => ⟨((-2717468015/17179869184), (10913683591/34359738368)), (73/34359738368), by norm_num⟩
  | 5 => ⟨((1628161327/17179869184), (-13077789663/68719476736)), (89/68719476736), by norm_num⟩
  | 6 => ⟨((-3251690289/68719476736), (816199095/8589934592)), (91/137438953472), by norm_num⟩
  | 7 => ⟨((2783198155/137438953472), (-22355327731/549755813888)), (79/274877906944), by norm_num⟩
  | 8 => ⟨((-8337716537/1099511627776), (523207631/34359738368)), (121/1099511627776), by norm_num⟩
  | 9 => ⟨((11101140675/4398046511104), (-22291768689/4398046511104)), (41/1099511627776), by norm_num⟩
  | 10 => ⟨((-6651209079/8796093022208), (13356034179/8796093022208)), (25/2199023255552), by norm_num⟩
  | 11 => ⟨((7245542435/35184372088832), (-3637372967/8796093022208)), (55/17592186044416), by norm_num⟩
  | 12 => ⟨((-226101097/4398046511104), (7264397059/70368744177664)), (7/8796093022208), by norm_num⟩
  | _ => zero

def term20ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581049060283875/10141204801825835211973625643008), (2647997029843/10141204801825835211973625643008)), (2427/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778498438463803/633825300114114700748351602688), (783219080333/158456325028528675187087900672)), (723/158456325028528675187087900672), by norm_num⟩
  | 16 => ⟨((1889437540460937/39614081257132168796771975168), (1761893705327/19807040628566084398385987584)), (1627/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((472298337130687/618970019642690137449562112), (3743165146477/2475880078570760549798248448)), (3457/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1770859321674637/154742504910672534362390528), (3742199033093/154742504910672534362390528)), (1729/77371252455336267181195264), by norm_num⟩
  | 13 => ⟨((1549242476623143/9671406556917033397649408), (3507285355695/9671406556917033397649408)), (3243/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((314629077583265/151115727451828646838272), (1533924369035/302231454903657293676544)), (2839/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((943674444660189/37778931862957161709568), (4983331162027/75557863725914323419136)), (4615/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648603303166601/2361183241434822606848), (466977041155/590295810358705651712)), (1731/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1620989670221297/590295810358705651712), (2567007643839/295147905179352825856)), (2381/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1822900394220829/73786976294838206464), (6413422880649/73786976294838206464)), (1489/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822009273749705/9223372036854775808), (1802367926371/2305843009213693952)), (3353/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1593255756828533/1152921504606846976), (7202440329619/1152921504606846976)), (839/144115188075855872), by norm_num⟩
  | 5 => ⟨((1193939652282597/144115188075855872), (3147115875607/72057594037927936)), (735/18014398509481984), by norm_num⟩
  | 4 => ⟨((1490671212475159/36028797018963968), (2356389362105/9007199254740992)), (69/281474976710656), by norm_num⟩
  | 3 => ⟨((372010516294483/2251799813685248), (11754351998831/9007199254740992)), (11063/9007199254740992), by norm_num⟩
  | 2 => ⟨((69546667417369/140737488355328), (2928258935853/562949953421312)), (5549/1125899906842624), by norm_num⟩
  | 1 => ⟨((2212363422360717/2251799813685248), (17466528668095/1125899906842624)), (33469/2251799813685248), by norm_num⟩
  | 0 => ⟨((2173022476381035/2251799813685248), (34522550281365/1125899906842624)), (16911/562949953421312), by norm_num⟩
  | _ => zero

def term20ValueSquares : ℕ → Disk
  | 0 => ⟨((2173022476381035/2251799813685248), (34522550281365/1125899906842624)), (64510347606468023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((65465125777895/70368744177664), (133259230678463/2251799813685248)), (8419/140737488355328), by norm_num⟩
  | 2 => ⟨((1941016705226671/2251799813685248), (247946226677161/2251799813685248)), (266579/2251799813685248), by norm_num⟩
  | 3 => ⟨((822912520047749/1125899906842624), (427451645615563/2251799813685248)), (518281/2251799813685248), by norm_num⟩
  | 4 => ⟨((1121780514375235/2251799813685248), (624842952298473/2251799813685248)), (59649/140737488355328), by norm_num⟩
  | 5 => ⟨((385452917315241/2251799813685248), (19454900147351/70368744177664)), (1480549/2251799813685248), by norm_num⟩
  | 6 => ⟨((-212277327831609/4503599627370496), (213132921597695/2251799813685248)), (5302099/9007199254740992), by norm_num⟩
  | _ => zero

def term20Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2412482277/1073741824), (-775104169/33554432)), (1/536870912), by norm_num⟩, -4, term20ValuePoly, term20ValueSquares⟩

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
  | 0 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-2451773307/1073741824), (-25207294309/1073741824)), (1/536870912), by norm_num⟩
  | 1 => ⟨((-6538062151/2147483648), 0), (1/8589934592), by norm_num⟩
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
  | 0 => ⟨((-157406997571547/18014398509481984), (1829590610605805/18014398509481984)), (9487995/18014398509481984), by norm_num⟩
  | 1 => ⟨((1828114075/68719476736), (-21248739875/68719476736)), (7/4294967296), by norm_num⟩
  | 2 => ⟨((-347858395/8589934592), (16173066331/34359738368)), (87/34359738368), by norm_num⟩
  | 3 => ⟨((1412083585/34359738368), (-16413087777/34359738368)), (45/17179869184), by norm_num⟩
  | 4 => ⟨((-2149560079/68719476736), (24985007005/68719476736)), (139/68719476736), by norm_num⟩
  | 5 => ⟨((2617753557/137438953472), (-30426965773/137438953472)), (43/34359738368), by norm_num⟩
  | 6 => ⟨((-2656603147/274877906944), (30878526669/274877906944)), (177/274877906944), by norm_num⟩
  | 7 => ⟨((1155441127/274877906944), (-26860104939/549755813888)), (39/137438953472), by norm_num⟩
  | 8 => ⟨((-879441609/549755813888), (10222024021/549755813888)), (121/1099511627776), by norm_num⟩
  | 9 => ⟨((1189990983/2199023255552), (-6915818109/1099511627776)), (83/2199023255552), by norm_num⟩
  | 10 => ⟨((-1449181699/8796093022208), (16844290727/8796093022208)), (103/8796093022208), by norm_num⟩
  | 11 => ⟨((1604387709/35184372088832), (-18648298569/35184372088832)), (29/8796093022208), by norm_num⟩
  | 12 => ⟨((-814099063/70368744177664), (18925054473/140737488355328)), (119/140737488355328), by norm_num⟩
  | _ => zero

def term21ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581001394306545/10141204801825835211973625643008), (1078965600929/5070602400912917605986812821504)), (607/2535301200456458802993406410752), by norm_num⟩
  | 17 => ⟨((889221905845089/316912650057057350374175801344), (2552919469251/633825300114114700748351602688)), (1445/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1889376196928497/39614081257132168796771975168), (1435729727707/19807040628566084398385987584)), (3251/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944564158131545/1237940039285380274899124224), (1525107337477/1237940039285380274899124224)), (27/19342813113834066795298816), by norm_num⟩
  | 14 => ⟨((1770794452684801/154742504910672534362390528), (1524707526917/77371252455336267181195264)), (27/1208925819614629174706176), by norm_num⟩
  | 13 => ⟨((774590917654723/4835703278458516698824704), (714494315177/2417851639229258349412352)), (3241/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258463422424207/604462909807314587353088), (2499881026615/604462909807314587353088)), (2837/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887263271032073/75557863725914323419136), (2030357617817/37778931862957161709568)), (2305/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((648571338173825/2361183241434822606848), (3044144508837/4722366482869645213696)), (3459/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1620902227061721/590295810358705651712), (4183437930803/590295810358705651712)), (2379/295147905179352825856), by norm_num⟩
  | 8 => ⟨((911395890133597/36893488147419103232), (5225908180485/73786976294838206464)), (2975/36893488147419103232), by norm_num⟩
  | 7 => ⟨((1821888030399821/9223372036854775808), (2937244813323/4611686018427387904)), (6697/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1593135695571185/1152921504606846976), (1467168239293/288230376151711744)), (3351/576460752303423488), by norm_num⟩
  | 5 => ⟨((596917962831413/72057594037927936), (5128551509885/144115188075855872)), (2935/72057594037927936), by norm_num⟩
  | 4 => ⟨((1490518269332167/36028797018963968), (7679768661281/36028797018963968)), (8815/36028797018963968), by norm_num⟩
  | 3 => ⟨((371963875502935/2251799813685248), (4788447176817/4503599627370496)), (11037/9007199254740992), by norm_num⟩
  | 2 => ⟨((2225134013993129/4503599627370496), (19085483455527/4503599627370496)), (22131/4503599627370496), by norm_num⟩
  | 1 => ⟨((2211858640250889/2251799813685248), (7114491473237/562949953421312)), (8335/562949953421312), by norm_num⟩
  | 0 => ⟨((2172148501933727/2251799813685248), (3514869480659/140737488355328)), (67255/2251799813685248), by norm_num⟩
  | _ => zero

def term21ValueSquares : ℕ → Disk
  | 0 => ⟨((2172148501933727/2251799813685248), (3514869480659/140737488355328)), (256557473189543967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1046955058590453/1125899906842624), (108497296152251/2251799813685248)), (133113/2251799813685248), by norm_num⟩
  | 2 => ⟨((1941863521342049/2251799813685248), (12611222405255/140737488355328)), (260387/2251799813685248), by norm_num⟩
  | 3 => ⟨((1656505575063655/2251799813685248), (348013497106993/2251799813685248)), (247881/1125899906842624), by norm_num⟩
  | 4 => ⟨((582400200521323/1125899906842624), (512022689274201/2251799813685248)), (882641/2251799813685248), by norm_num⟩
  | 5 => ⟨((243048412493235/1125899906842624), (1059426739774813/4503599627370496)), (2629067/4503599627370496), by norm_num⟩
  | 6 => ⟨((-157406997571547/18014398509481984), (1829590610605805/18014398509481984)), (9487995/18014398509481984), by norm_num⟩
  | _ => zero

def term21Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2451773307/1073741824), (-25207294309/1073741824)), (1/536870912), by norm_num⟩, -4, term21ValuePoly, term21ValueSquares⟩

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
theorem term16Jet_sound : Sound term16Jet F_term16 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term16

def term17Jet : Jet 12 := J_term17
theorem term17Jet_sound : Sound term17Jet F_term17 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term17

def term18Jet : Jet 12 := J_term18
theorem term18Jet_sound : Sound term18Jet F_term18 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term18

def term19Jet : Jet 12 := J_term19
theorem term19Jet_sound : Sound term19Jet F_term19 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term19

def term20Jet : Jet 12 := J_term20
theorem term20Jet_sound : Sound term20Jet F_term20 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term20

def term21Jet : Jet 12 := J_term21
theorem term21Jet_sound : Sound term21Jet F_term21 (Data.centre ⟨17,by norm_num [Data.count]⟩) := S_term21

end Reinmann.XiRectangle.Tile017Terms2
