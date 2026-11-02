/-
Copyright (c) 2026 Biswajit Mondal. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Biswajit Mondal
-/
-- Internal rounding: 32 bits, checked against fixed final error disks.
module

public import Reinmann.RectangleModel
public import XiRectangle.Data

@[expose] public section

/-! Numerical proposals for one closed ball. Every rounding check is proved
by rational arithmetic in the Lean kernel; no native evaluation is used. -/
noncomputable section
namespace Reinmann.XiRectangle.Tile023Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨23,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (6627/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (6627/640))
  have he : value ((3/4), (6627/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-55294967/33554432), (-3053664553/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-4718503851/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-627974528505405/4503599627370496), (18667745289025/140737488355328)), (19581203/4503599627370496), by norm_num⟩
  | 1 => ⟨((2631761681/8589934592), (-1251746483/4294967296)), (21/2147483648), by norm_num⟩
  | 2 => ⟨((-722821431/2147483648), (2750368137/8589934592)), (47/4294967296), by norm_num⟩
  | 3 => ⟨((2117601351/8589934592), (-503598039/2147483648)), (35/4294967296), by norm_num⟩
  | 4 => ⟨((-2326422867/17179869184), (2213035977/17179869184)), (79/17179869184), by norm_num⟩
  | 5 => ⟨((4089338801/68719476736), (-60781713/1073741824)), (71/34359738368), by norm_num⟩
  | 6 => ⟨((-374383155/17179869184), (2849089571/137438953472)), (107/137438953472), by norm_num⟩
  | 7 => ⟨((235029677/34359738368), (-1788597037/274877906944)), (137/549755813888), by norm_num⟩
  | 8 => ⟨((-2065651931/1099511627776), (3929949369/2199023255552)), (153/2199023255552), by norm_num⟩
  | 9 => ⟨((4034401059/8796093022208), (-3837769485/8796093022208)), (19/1099511627776), by norm_num⟩
  | 10 => ⟨((-3545794065/35184372088832), (1686488287/17592186044416)), (17/4398046511104), by norm_num⟩
  | 11 => ⟨((2833056679/140737488355328), (-2694977101/140737488355328)), (111/140737488355328), by norm_num⟩
  | 12 => ⟨((-4149907843/1125899906842624), (3947646615/1125899906842624)), (165/1125899906842624), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (387717043241/1267650600228229401496703205376)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((222427486878185/79228162514264337593543950336), (3673328691065/633825300114114700748351602688)), (11571/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890473880157843/39614081257132168796771975168), (4131878153141/39614081257132168796771975168)), (3255/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((1890294095204557/2475880078570760549798248448), (68584071371/38685626227668133590597632)), (13837/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((221494957326721/19342813113834066795298816), (4388548105793/154742504910672534362390528)), (13841/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550273607234241/9671406556917033397649408), (4113379427845/9671406556917033397649408)), (3245/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((1259418114440747/604462909807314587353088), (1799161328027/302231454903657293676544)), (5681/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944406752617371/37778931862957161709568), (1461404084595/18889465931478580854784)), (9235/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((1298304354674857/4722366482869645213696), (136961302797/147573952589676412928)), (13859/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622497914969227/590295810358705651712), (6023940468223/590295810358705651712)), (19067/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1824783961968599/73786976294838206464), (7526390850129/73786976294838206464)), (23849/73786976294838206464), by norm_num⟩
  | 7 => ⟨((912062949254427/4611686018427387904), (8462330336351/9223372036854775808)), (6713/2305843009213693952), by norm_num⟩
  | 6 => ⟨((1595369396968557/1152921504606846976), (8456257462985/1152921504606846976)), (105/4503599627370496), by norm_num⟩
  | 5 => ⟨((597892865940193/72057594037927936), (7392395143849/144115188075855872)), (23/140737488355328), by norm_num⟩
  | 4 => ⟨((1493433626261029/36028797018963968), (2768734268389/9007199254740992)), (35389/36028797018963968), by norm_num⟩
  | 3 => ⟨((745741679926753/4503599627370496), (3454946106603/2251799813685248)), (44345/9007199254740992), by norm_num⟩
  | 2 => ⟨((558085207052661/1125899906842624), (6891987534959/1125899906842624)), (44509/2251799813685248), by norm_num⟩
  | 1 => ⟨((555636751267973/562949953421312), (10293256610793/562949953421312)), (33587/562949953421312), by norm_num⟩
  | 0 => ⟨((1096520093995261/1125899906842624), (40815676536799/1125899906842624)), (33999/281474976710656), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((1096520093995261/1125899906842624), (40815676536799/1125899906842624)), (129695893407726199/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((533213649715689/562949953421312), (79501222445463/1125899906842624)), (68689/281474976710656), by norm_num⟩
  | 2 => ⟨((1004482488833051/1125899906842624), (37650893049527/281474976710656)), (69911/140737488355328), by norm_num⟩
  | 3 => ⟨((27375425104931/35184372088832), (268724866410081/1125899906842624)), (1147573/1125899906842624), by norm_num⟩
  | 4 => ⟨((1234899790320275/2251799813685248), (209083096201589/562949953421312)), (2333549/1125899906842624), by norm_num⟩
  | 5 => ⟨((366607026628239/2251799813685248), (229324711805795/562949953421312)), (8585705/2251799813685248), by norm_num⟩
  | 6 => ⟨((-627974528505405/4503599627370496), (18667745289025/140737488355328)), (19581203/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-3053664553/134217728)), (1/134217728), by norm_num⟩, -4, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-231785805/134217728), (-3200092767/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-4944763835/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((443577561056925/9007199254740992), (1539085238160767/9007199254740992)), (29056335/9007199254740992), by norm_num⟩
  | 1 => ⟨((-974059181/8589934592), (-3379702307/8589934592)), (33/4294967296), by norm_num⟩
  | 2 => ⟨((1121427075/8589934592), (3891026075/8589934592)), (39/4294967296), by norm_num⟩
  | 3 => ⟨((-1721454177/17179869184), (-5972945757/17179869184)), (61/8589934592), by norm_num⟩
  | 4 => ⟨((990948681/17179869184), (3438303965/17179869184)), (9/2147483648), by norm_num⟩
  | 5 => ⟨((-1825394929/68719476736), (-1583397491/17179869184)), (17/8589934592), by norm_num⟩
  | 6 => ⟨((87565149/8589934592), (4861209945/137438953472)), (53/68719476736), by norm_num⟩
  | 7 => ⟨((-460859901/137438953472), (-99940621/8589934592)), (71/274877906944), by norm_num⟩
  | 8 => ⟨((530584569/549755813888), (3681948545/1099511627776)), (21/274877906944), by norm_num⟩
  | 9 => ⟨((-271492471/1099511627776), (-3767999925/4398046511104)), (11/549755813888), by norm_num⟩
  | 10 => ⟨((500107613/8796093022208), (3470456183/17592186044416)), (83/17592186044416), by norm_num⟩
  | 11 => ⟨((-1674967759/140737488355328), (-2905825699/70368744177664)), (141/140737488355328), by norm_num⟩
  | 12 => ⟨((80349079/35184372088832), (4460607291/562949953421312)), (55/281474976710656), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581726236476819/10141204801825835211973625643008), (420154831699/2535301200456458802993406410752)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1779303096622047/633825300114114700748351602688), (995033421809/316912650057057350374175801344)), (5775/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890342796656071/39614081257132168796771975168), (279810322879/4951760157141521099596496896)), (12995/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945077609620643/1237940039285380274899124224), (2377968472289/2475880078570760549798248448)), (6905/1237940039285380274899124224), by norm_num⟩
  | 14 => ⟨((1771821232705699/154742504910672534362390528), (297187111953/19342813113834066795298816)), (3453/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((1550144310898553/9671406556917033397649408), (1114201198697/4835703278458516698824704)), (6475/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((629652728920475/302231454903657293676544), (1949351276889/604462909807314587353088)), (5667/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((944315666692771/37778931862957161709568), (3166757043861/75557863725914323419136)), (18421/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((324542127118065/1180591620717411303424), (2374246607367/4722366482869645213696)), (3455/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((25348631207357/9223372036854775808), (3263255158373/590295810358705651712)), (297/9223372036854775808), by norm_num⟩
  | 8 => ⟨((1824553969285965/73786976294838206464), (4077068903681/73786976294838206464)), (2971/9223372036854775808), by norm_num⟩
  | 7 => ⟨((911934886207323/4611686018427387904), (1145988457453/2305843009213693952)), (26751/9223372036854775808), by norm_num⟩
  | 6 => ⟨((12461847938057/9007199254740992), (2290260015795/576460752303423488)), (13383/576460752303423488), by norm_num⟩
  | 5 => ⟨((1195568145902153/144115188075855872), (4004094836309/144115188075855872)), (11719/72057594037927936), by norm_num⟩
  | 4 => ⟨((1493114566819517/36028797018963968), (2999214473585/18014398509481984)), (35189/36028797018963968), by norm_num⟩
  | 3 => ⟨((186387163850653/1125899906842624), (1871138451337/2251799813685248)), (44045/9007199254740992), by norm_num⟩
  | 2 => ⟨((139475432522785/281474976710656), (1866090507405/562949953421312)), (22067/1125899906842624), by norm_num⟩
  | 1 => ⟨((2221541145345979/2251799813685248), (11146174760313/1125899906842624)), (8303/140737488355328), by norm_num⟩
  | 0 => ⟨((273925705106067/281474976710656), (44183084750727/2251799813685248)), (33435/281474976710656), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((273925705106067/281474976710656), (44183084750727/2251799813685248)), (127544404149913699/1073741824000000000000000000), by norm_num⟩
  | 1 => ⟨((532941084348503/562949953421312), (85996153445251/2251799813685248)), (531109/2251799813685248), by norm_num⟩
  | 2 => ⟨((2014843337406781/2251799813685248), (40706001473467/562949953421312)), (523081/1125899906842624), by norm_num⟩
  | 3 => ⟨((1791048206366405/2251799813685248), (72845032993461/562949953421312)), (2023443/2251799813685248), by norm_num⟩
  | 4 => ⟨((1386868973538223/2251799813685248), (231759439525163/1125899906842624)), (116953/70368744177664), by norm_num⟩
  | 5 => ⟨((758751194552551/2251799813685248), (285478286345559/1125899906842624)), (3075349/1125899906842624), by norm_num⟩
  | 6 => ⟨((443577561056925/9007199254740992), (1539085238160767/9007199254740992)), (29056335/9007199254740992), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-231785805/134217728), (-3200092767/134217728)), (1/134217728), by norm_num⟩, -4, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-482760083/268435456), (-6665106399/268435456)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-643680111/268435456), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((355793280885059/2251799813685248), (445366781732921/9007199254740992)), (22568391/9007199254740992), by norm_num⟩
  | 1 => ⟨((-1627264073/4294967296), (-2036939431/17179869184)), (53/8589934592), by norm_num⟩
  | 2 => ⟨((975502207/2147483648), (610545929/4294967296)), (65/8589934592), by norm_num⟩
  | 3 => ⟨((-6237739015/17179869184), (-488008399/4294967296)), (53/8589934592), by norm_num⟩
  | 4 => ⟨((467420153/2147483648), (1170193033/17179869184)), (65/17179869184), by norm_num⟩
  | 5 => ⟨((-3586638641/34359738368), (-1122400137/34359738368)), (1/536870912), by norm_num⟩
  | 6 => ⟨((1433397307/34359738368), (897132661/68719476736)), (105/137438953472), by norm_num⟩
  | 7 => ⟨((-3928156145/274877906944), (-1229274381/274877906944)), (37/137438953472), by norm_num⟩
  | 8 => ⟨((4709653525/1099511627776), (736917807/549755813888)), (91/1099511627776), by norm_num⟩
  | 9 => ⟨((-5019224855/4398046511104), (-1570712645/4398046511104)), (99/4398046511104), by norm_num⟩
  | 10 => ⟨((4814230221/17592186044416), (1506561771/17592186044416)), (97/17592186044416), by norm_num⟩
  | 11 => ⟨((-2098912707/35184372088832), (-1313664491/70368744177664)), (87/70368744177664), by norm_num⟩
  | 12 => ⟨((3355315239/281474976710656), (525004979/140737488355328)), (71/281474976710656), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581633122367159/10141204801825835211973625643008), (24691412719/633825300114114700748351602688)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1779194844677447/633825300114114700748351602688), (14617161491/19807040628566084398385987584)), (17297/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472555286840019/9903520314283042199192993792), (65766838137/4951760157141521099596496896)), (4865/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((472506534449363/618970019642690137449562112), (139728894263/618970019642690137449562112)), (5169/618970019642690137449562112), by norm_num⟩
  | 14 => ⟨((1771692343445765/154742504910672534362390528), (558800247655/154742504910672534362390528)), (20677/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1550023681312227/9671406556917033397649408), (130938182019/2417851639229258349412352)), (19385/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629600055467329/302231454903657293676544), (14317536579/18889465931478580854784)), (16963/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888460526888323/75557863725914323419136), (186070589285/18889465931478580854784)), (13783/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((324510184451631/1180591620717411303424), (558010995767/4722366482869645213696)), (20677/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622137255242135/590295810358705651712), (383469507007/295147905179352825856)), (28431/590295810358705651712), by norm_num⟩
  | 8 => ⟨((228041981864767/9223372036854775808), (958184871221/73786976294838206464)), (17771/36893488147419103232), by norm_num⟩
  | 7 => ⟨((455906377644785/2305843009213693952), (269321543079/2305843009213693952)), (39989/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797436834178121/576460752303423488), (67277940563/72057594037927936)), (39995/1152921504606846976), by norm_num⟩
  | 5 => ⟨((298839300601707/36028797018963968), (940948028551/144115188075855872)), (35001/144115188075855872), by norm_num⟩
  | 4 => ⟨((746400638260183/18014398509481984), (88096121747/2251799813685248)), (52513/36028797018963968), by norm_num⟩
  | 3 => ⟨((186338893978883/1125899906842624), (1758630176423/9007199254740992)), (65663/9007199254740992), by norm_num⟩
  | 2 => ⟨((2230850905225153/4503599627370496), (3507403177331/4503599627370496)), (131389/4503599627370496), by norm_num⟩
  | 1 => ⟨((277555959258723/281474976710656), (5236530292457/2251799813685248)), (49311/562949953421312), by norm_num⟩
  | 0 => ⟨((2189379674700285/2251799813685248), (10375172405335/2251799813685248)), (197567/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2189379674700285/2251799813685248), (10375172405335/2251799813685248)), (753658298972701671/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((2128642025217913/2251799813685248), (20175142965819/2251799813685248)), (193001/562949953421312), by norm_num⟩
  | 2 => ⟨((1006019675371423/1125899906842624), (19071702964367/1125899906842624)), (368349/562949953421312), by norm_num⟩
  | 3 => ⟨((1797161277360115/2251799813685248), (68164170929893/2251799813685248)), (2682949/2251799813685248), by norm_num⟩
  | 4 => ⟨((1432250896835221/2251799813685248), (54401820159171/1125899906842624)), (4444955/2251799813685248), by norm_num⟩
  | 5 => ⟨((1811443794376163/4503599627370496), (138408494820725/2251799813685248)), (3041975/1125899906842624), by norm_num⟩
  | 6 => ⟨((355793280885059/2251799813685248), (445366781732921/9007199254740992)), (22568391/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-482760083/268435456), (-6665106399/268435456)), (3/268435456), by norm_num⟩, -4, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-500277787/268435456), (-863370025/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5336296397/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((1154832205002571/9007199254740992), (-393077077638245/4503599627370496)), (17574253/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2736711717/8589934592), (1863021553/8589934592)), (43/8589934592), by norm_num⟩
  | 2 => ⟨((850059143/2147483648), (-2314717323/8589934592)), (55/8589934592), by norm_num⟩
  | 3 => ⟨((-2816423489/8589934592), (1917285489/8589934592)), (3/536870912), by norm_num⟩
  | 4 => ⟨((437409341/2147483648), (-1191068865/8589934592)), (31/8589934592), by norm_num⟩
  | 5 => ⟨((-54346069/536870912), (1183877977/17179869184)), (1/536870912), by norm_num⟩
  | 6 => ⟨((2880958043/68719476736), (-1961217505/68719476736)), (55/68719476736), by norm_num⟩
  | 7 => ⟨((-2045403371/137438953472), (174051515/17179869184)), (5/17179869184), by norm_num⟩
  | 8 => ⟨((2541318219/549755813888), (-432501767/137438953472)), (51/549755813888), by norm_num⟩
  | 9 => ⟨((-350829919/274877906944), (1910624919/2199023255552)), (29/1099511627776), by norm_num⟩
  | 10 => ⟨((697423679/2199023255552), (-1899089827/8796093022208)), (15/2199023255552), by norm_num⟩
  | 11 => ⟨((-2520774891/35184372088832), (107251385/2199023255552)), (111/70368744177664), by norm_num⟩
  | 12 => ⟨((4175926859/281474976710656), (-1421384959/140737488355328)), (47/140737488355328), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581548115842083/10141204801825835211973625643008), (-389279367029/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((889546933006381/316912650057057350374175801344), (-460852271461/316912650057057350374175801344)), (11537/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890107545322999/39614081257132168796771975168), (-1036747960127/39614081257132168796771975168)), (3245/9903520314283042199192993792), by norm_num⟩
  | 15 => ⟨((944952716639663/1237940039285380274899124224), (-1101335292217/2475880078570760549798248448)), (431/77371252455336267181195264), by norm_num⟩
  | 14 => ⟨((1771571636292381/154742504910672534362390528), (-550549887033/77371252455336267181195264)), (13793/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774955257782789/4835703278458516698824704), (-1032030869045/9671406556917033397649408)), (3233/2417851639229258349412352), by norm_num⟩
  | 12 => ⟨((629550544063403/302231454903657293676544), (-902776918785/604462909807314587353088)), (11317/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888299609636911/75557863725914323419136), (-1466543735875/75557863725914323419136)), (18391/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((20280000708607/73786976294838206464), (-1099497803991/4722366482869645213696)), (13795/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((202746411977283/73786976294838206464), (-1511143542341/590295810358705651712)), (9485/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824128394767495/73786976294838206464), (-1887931060249/73786976294838206464)), (23717/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823392103084319/9223372036854775808), (-2122550563455/9223372036854775808)), (26687/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594640242512487/1152921504606846976), (-2120837027737/1152921504606846976)), (13347/576460752303423488), by norm_num⟩
  | 5 => ⟨((18674264600029/2251799813685248), (-1853806476085/144115188075855872)), (23365/144115188075855872), by norm_num⟩
  | 4 => ⟨((746247417177727/18014398509481984), (-2776862374569/36028797018963968)), (35063/36028797018963968), by norm_num⟩
  | 3 => ⟨((745164015127129/4503599627370496), (-3464355252129/9007199254740992)), (2741/562949953421312), by norm_num⟩
  | 2 => ⟨((1115042230530975/2251799813685248), (-6908582807759/4503599627370496)), (87795/4503599627370496), by norm_num⟩
  | 1 => ⟨((277412190604069/281474976710656), (-10312696278159/2251799813685248)), (131899/2251799813685248), by norm_num⟩
  | 0 => ⟨((2187077560832295/2251799813685248), (-10212763243061/1125899906842624)), (264635/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2187077560832295/2251799813685248), (-10212763243061/1125899906842624)), (1009502419478606467/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2124030309397853/2251799813685248), (-9919223364015/562949953421312)), (129715/562949953421312), by norm_num⟩
  | 2 => ⟨((1001405735971165/1125899906842624), (-18712792267599/562949953421312)), (249281/562949953421312), by norm_num⟩
  | 3 => ⟨((1778866429550429/2251799813685248), (-133149296124277/2251799813685248)), (1840029/2251799813685248), by norm_num⟩
  | 4 => ⟨((698693778194559/1125899906842624), (-210369333503153/2251799813685248)), (3124759/2251799813685248), by norm_num⟩
  | 5 => ⟨((1695032315638469/4503599627370496), (-522191159438951/4503599627370496)), (2231039/1125899906842624), by norm_num⟩
  | 6 => ⟨((1154832205002571/9007199254740992), (-393077077638245/4503599627370496)), (17574253/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-500277787/268435456), (-863370025/33554432)), (1/134217728), by norm_num⟩, -4, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-516392513/268435456), (-3564722065/134217728)), (3/268435456), by norm_num⟩
  | 1 => ⟨((-5508186803/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((94585813465971/4503599627370496), (-650977022832573/4503599627370496)), (37783877/9007199254740992), by norm_num⟩
  | 1 => ⟨((-925475393/17179869184), (3184744065/8589934592)), (187/17179869184), by norm_num⟩
  | 2 => ⟨((593449379/8589934592), (-2042176811/4294967296)), (61/4294967296), by norm_num⟩
  | 3 => ⟨((-507389201/8589934592), (6984106799/17179869184)), (211/17179869184), by norm_num⟩
  | 4 => ⟨((650713803/17179869184), (-2239235031/8589934592)), (69/8589934592), by norm_num⟩
  | 5 => ⟨((-166904795/8589934592), (4594819563/34359738368)), (143/34359738368), by norm_num⟩
  | 6 => ⟨((570803129/68719476736), (-1964246581/34359738368)), (31/17179869184), by norm_num⟩
  | 7 => ⟨((-418308891/137438953472), (359870929/17179869184)), (23/34359738368), by norm_num⟩
  | 8 => ⟨((1072941121/1099511627776), (-7384405665/1099511627776)), (119/549755813888), by norm_num⟩
  | 9 => ⟨((-152891091/549755813888), (2104514063/1099511627776)), (69/1099511627776), by norm_num⟩
  | 10 => ⟨((627452649/8796093022208), (-4318377595/8796093022208)), (143/8796093022208), by norm_num⟩
  | 11 => ⟨((-585230643/35184372088832), (503473629/4398046511104)), (135/35184372088832), by norm_num⟩
  | 12 => ⟨((1000724641/281474976710656), (-1721845815/70368744177664)), (233/281474976710656), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917417231/10141204801825835211973625643008), (-1858185708837/10141204801825835211973625643008)), (14559/10141204801825835211973625643008), by norm_num⟩
  | 17 => ⟨((1778999160450511/633825300114114700748351602688), (-2199613860921/633825300114114700748351602688)), (17329/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118125056097661/2475880078570760549798248448), (-2474145307073/39614081257132168796771975168)), (9749/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889791984479515/2475880078570760549798248448), (-657065801091/618970019642690137449562112)), (20719/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771458035118833/154742504910672534362390528), (-82115082601/4835703278458516698824704)), (20723/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((96862740792011/604462909807314587353088), (-2462835780379/9671406556917033397649408)), (19431/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629503798209397/302231454903657293676544), (-1077182388631/302231454903657293676544)), (8503/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888147382716667/75557863725914323419136), (-1749843561603/37778931862957161709568)), (27641/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648902805187971/2361183241434822606848), (-1311877256213/2361183241434822606848)), (20737/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810906758958785/295147905179352825856), (-1803010260549/295147905179352825856)), (14261/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823930528489403/73786976294838206464), (-4505063914917/73786976294838206464)), (35667/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823168619475945/9223372036854775808), (-5064813907099/9223372036854775808)), (40145/9223372036854775808), by norm_num⟩
  | 6 => ⟨((1594415655825169/1152921504606846976), (-2530293997539/576460752303423488)), (20085/576460752303423488), by norm_num⟩
  | 5 => ⟨((149369397850365/18014398509481984), (-1105816060019/36028797018963968)), (35177/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492195737242447/36028797018963968), (-6625405581491/36028797018963968)), (52821/36028797018963968), by norm_num⟩
  | 3 => ⟨((186243731511301/1125899906842624), (-8265169996399/9007199254740992)), (16531/2251799813685248), by norm_num⟩
  | 2 => ⟨((1114657622594021/2251799813685248), (-515020828083/140737488355328)), (132543/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218111764226577/2251799813685248), (-24597121712351/2251799813685248)), (99777/1125899906842624), by norm_num⟩
  | 0 => ⟨((2184579559832405/2251799813685248), (-24350281277409/1125899906842624)), (100519/562949953421312), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((2184579559832405/2251799813685248), (-24350281277409/1125899906842624)), (383449556590843023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((2118312684571139/2251799813685248), (-5905845452103/140737488355328)), (797539/2251799813685248), by norm_num⟩
  | 2 => ⟨((994386706959711/1125899906842624), (-88891932636461/1125899906842624)), (783729/1125899906842624), by norm_num⟩
  | 3 => ⟨((871217007239207/1125899906842624), (-157017432246773/1125899906842624)), (754061/562949953421312), by norm_num⟩
  | 4 => ⟨((326123394810849/562949953421312), (-485997934896497/2251799813685248)), (5509205/2251799813685248), by norm_num⟩
  | 5 => ⟨((650816958353489/2251799813685248), (-281544203772035/1125899906842624)), (8761157/2251799813685248), by norm_num⟩
  | 6 => ⟨((94585813465971/4503599627370496), (-650977022832573/4503599627370496)), (37783877/9007199254740992), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-516392513/268435456), (-3564722065/134217728)), (3/268435456), by norm_num⟩, -4, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-265656209/134217728), (-3667716037/134217728)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5667332461/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-726208879000545/9007199254740992), (-126329966091595/1125899906842624)), (14029709/4503599627370496), by norm_num⟩
  | 1 => ⟨((913861687/4294967296), (2543579277/8589934592)), (73/8589934592), by norm_num⟩
  | 2 => ⟨((-2411733383/8589934592), (-3356325767/8589934592)), (49/4294967296), by norm_num⟩
  | 3 => ⟨((1060783777/4294967296), (1476256019/4294967296)), (11/1073741824), by norm_num⟩
  | 4 => ⟨((-1399734601/8589934592), (-3895924267/17179869184)), (59/8589934592), by norm_num⟩
  | 5 => ⟨((1477591943/17179869184), (4112626997/34359738368)), (127/34359738368), by norm_num⟩
  | 6 => ⟨((-2599633231/68719476736), (-3617819473/68719476736)), (57/34359738368), by norm_num⟩
  | 7 => ⟨((980083019/68719476736), (1363947571/68719476736)), (11/17179869184), by norm_num⟩
  | 8 => ⟨((-2586495275/549755813888), (-1799767917/274877906944)), (59/274877906944), by norm_num⟩
  | 9 => ⟨((11850537/8589934592), (1055486825/549755813888)), (141/2199023255552), by norm_num⟩
  | 10 => ⟨((-800620711/2199023255552), (-4456784387/8796093022208)), (19/1099511627776), by norm_num⟩
  | 11 => ⟨((3073285753/35184372088832), (4276985273/35184372088832)), (37/8796093022208), by norm_num⟩
  | 12 => ⟨((-675881441/35184372088832), (-3762403111/140737488355328)), (33/35184372088832), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((197674689623573/1267650600228229401496703205376), (-1428882076997/5070602400912917605986812821504)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778909926860331/633825300114114700748351602688), (-3382547369245/633825300114114700748351602688)), (11567/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((118118770391813/2475880078570760549798248448), (-951173557759/9903520314283042199192993792)), (1627/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((236210611015965/309485009821345068724781056), (-252604379197/154742504910672534362390528)), (1729/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((221418833713331/19342813113834066795298816), (-126273451547/4835703278458516698824704)), (3459/38685626227668133590597632), by norm_num⟩
  | 13 => ⟨((774851455953461/4835703278458516698824704), (-1893613314377/4835703278458516698824704)), (12975/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629459493883161/302231454903657293676544), (-1656423290209/302231454903657293676544)), (11357/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944001429409389/37778931862957161709568), (-2690772382145/37778931862957161709568)), (18461/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297696749912151/4722366482869645213696), (-1008639232785/1180591620717411303424)), (3463/1180591620717411303424), by norm_num⟩
  | 9 => ⟨((1621663075856045/590295810358705651712), (-2772456950451/295147905179352825856)), (19057/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911870669488547/36893488147419103232), (-3463620468993/36893488147419103232)), (5959/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1822954220343401/9223372036854775808), (-7787783822443/9223372036854775808)), (26835/9223372036854775808), by norm_num⟩
  | 6 => ⟨((24909364204031/18014398509481984), (-7781084399405/1152921504606846976)), (6715/288230376151711744), by norm_num⟩
  | 5 => ⟨((1194763693140453/144115188075855872), (-6800916631069/144115188075855872)), (5883/36028797018963968), by norm_num⟩
  | 4 => ⟨((745952071185335/18014398509481984), (-10186322095749/36028797018963968)), (35355/36028797018963968), by norm_num⟩
  | 3 => ⟨((1489577755031905/9007199254740992), (-12706586211949/9007199254740992)), (22147/4503599627370496), by norm_num⟩
  | 2 => ⟨((1114274174613643/2251799813685248), (-12667163794711/2251799813685248)), (22223/1125899906842624), by norm_num⟩
  | 1 => ⟨((1108452522352995/1125899906842624), (-18902372471269/1125899906842624)), (67047/1125899906842624), by norm_num⟩
  | 0 => ⟨((1090971442572419/1125899906842624), (-37412350116063/1125899906842624)), (67807/562949953421312), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((1090971442572419/1125899906842624), (-37412350116063/1125899906842624)), (258663179637718023/2147483648000000000000000000), by norm_num⟩
  | 1 => ⟨((527941692393047/562949953421312), (-72503435390817/1125899906842624)), (271827/1125899906842624), by norm_num⟩
  | 2 => ⟨((1971104122808975/2251799813685248), (-271978609479631/2251799813685248)), (1089711/2251799813685248), by norm_num⟩
  | 3 => ⟨((105784245222897/140737488355328), (-238075407593087/1125899906842624)), (1085493/1125899906842624), by norm_num⟩
  | 4 => ⟨((585753417940163/1125899906842624), (-178947539796811/562949953421312)), (522717/281474976710656), by norm_num⟩
  | 5 => ⟨((95487253051755/562949953421312), (-744784735701141/2251799813685248)), (7009663/2251799813685248), by norm_num⟩
  | 6 => ⟨((-726208879000545/9007199254740992), (-126329966091595/1125899906842624)), (14029709/4503599627370496), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-265656209/134217728), (-3667716037/134217728)), (1/134217728), by norm_num⟩, -4, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-272601259/134217728), (-940900283/33554432)), (1/134217728), by norm_num⟩
  | 1 => ⟨((-5815493525/2147483648), 0), (1/2147483648), by norm_num⟩
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
  | 0 => ⟨((-1149718043353277/9007199254740992), (-273228703799069/9007199254740992)), (25388533/9007199254740992), by norm_num⟩
  | 1 => ⟨((5938518865/17179869184), (1411279767/17179869184)), (133/17179869184), by norm_num⟩
  | 2 => ⟨((-2010225901/4294967296), (-477727057/4294967296)), (23/2147483648), by norm_num⟩
  | 3 => ⟨((113412347/268435456), (862472569/8589934592)), (85/8589934592), by norm_num⟩
  | 4 => ⟨((-2457010633/8589934592), (-1167809507/17179869184)), (117/17179869184), by norm_num⟩
  | 5 => ⟨((5322966511/34359738368), (316248677/8589934592)), (129/34359738368), by norm_num⟩
  | 6 => ⟨((-2402476755/34359738368), (-285472431/17179869184)), (119/68719476736), by norm_num⟩
  | 7 => ⟨((3717730091/137438953472), (883512771/137438953472)), (47/68719476736), by norm_num⟩
  | 8 => ⟨((-1258474965/137438953472), (-1196298469/549755813888)), (65/274877906944), by norm_num⟩
  | 9 => ⟨((6058690457/2199023255552), (179979795/274877906944)), (159/2199023255552), by norm_num⟩
  | 10 => ⟨((-1640723791/2199023255552), (-6092429/34359738368)), (175/8796093022208), by norm_num⟩
  | 11 => ⟨((3231390831/17592186044416), (767935003/17592186044416)), (175/35184372088832), by norm_num⟩
  | 12 => ⟨((-5833845727/140737488355328), (-173300545/17592186044416)), (5/4398046511104), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798419/10141204801825835211973625643008), (-3788349433041/10141204801825835211973625643008)), (4853/5070602400912917605986812821504), by norm_num⟩
  | 17 => ⟨((1778825512845451/633825300114114700748351602688), (-1120909265115/158456325028528675187087900672)), (11581/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472451278737351/9903520314283042199192993792), (-2521583301207/19807040628566084398385987584)), (1629/4951760157141521099596496896), by norm_num⟩
  | 15 => ⟨((1889583404974153/2475880078570760549798248448), (-5357251057031/2475880078570760549798248448)), (13851/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771248825554831/154742504910672534362390528), (-5355998410213/154742504910672534362390528)), (13855/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((774803524855089/4835703278458516698824704), (-627489713385/1208925819614629174706176)), (12995/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258834725327737/604462909807314587353088), (-4391097342335/604462909807314587353088)), (11375/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((235983151851503/9444732965739290427392), (-7133038531585/75557863725914323419136)), (18493/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1297592889667581/4722366482869645213696), (-1336899100565/1180591620717411303424)), (6939/2361183241434822606848), by norm_num⟩
  | 9 => ⟨((1621519249901735/590295810358705651712), (-459337443831/36893488147419103232)), (19095/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911780015681009/36893488147419103232), (-9181431009477/73786976294838206464)), (1493/4611686018427387904), by norm_num⟩
  | 7 => ⟨((1822748155420791/9223372036854775808), (-10321799545559/9223372036854775808)), (26901/9223372036854775808), by norm_num⟩
  | 6 => ⟨((796995315848435/576460752303423488), (-10312664217871/1152921504606846976)), (26935/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194578168162567/144115188075855872), (-4506653764599/72057594037927936)), (23607/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491620007080861/36028797018963968), (-1687427869819/4503599627370496)), (17743/18014398509481984), by norm_num⟩
  | 3 => ⟨((1489212389877021/9007199254740992), (-8419178460881/4503599627370496)), (22245/4503599627370496), by norm_num⟩
  | 2 => ⟨((278473397646335/562949953421312), (-16784515097103/2251799813685248)), (11173/562949953421312), by norm_num⟩
  | 1 => ⟨((69240241363853/70368744177664), (-25042312007805/1125899906842624)), (16885/281474976710656), by norm_num⟩
  | 0 => ⟨((1089604555934317/1125899906842624), (-12386913209889/281474976710656)), (137099/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((1089604555934317/1125899906842624), (-12386913209889/281474976710656)), (522991184714889171/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((1052298797797589/1125899906842624), (-11987599417525/140737488355328)), (277427/1125899906842624), by norm_num⟩
  | 2 => ⟨((487670258530745/562949953421312), (-179263344869307/1125899906842624)), (141461/281474976710656), by norm_num⟩
  | 3 => ⟨((204093137369919/281474976710656), (-155291604886367/562949953421312)), (290135/281474976710656), by norm_num⟩
  | 4 => ⟨((1012527323054279/2251799813685248), (-450398130858339/1125899906842624)), (2323257/1125899906842624), by norm_num⟩
  | 5 => ⟨((94936358689389/2251799813685248), (-1620181016003545/4503599627370496)), (15792319/4503599627370496), by norm_num⟩
  | 6 => ⟨((-1149718043353277/9007199254740992), (-273228703799069/9007199254740992)), (25388533/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-272601259/134217728), (-940900283/33554432)), (1/134217728), by norm_num⟩, -4, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨23,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile023Terms1
