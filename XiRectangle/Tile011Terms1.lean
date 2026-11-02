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
namespace Reinmann.XiRectangle.Tile011Terms1
open CertifiedTaylorModel CertifiedTaylorComposition RectangleTaylor RectangleModel
open scoped Topology
set_option maxRecDepth 30000
set_option linter.style.longLine false
set_option linter.style.whitespace false

def c : ℂ := Data.centre ⟨11,by norm_num [Data.count]⟩
theorem hc : c ∈ XiAdaptiveTiles.quarter (141/10) := Data.centre_mem_quarter _
theorem hcre : -2<c.re := by linarith [hc.1]

def J_variable : Jet 12 := fun k =>
  match k.val with
  | 0 => ⟨((3/4), (3243/640)), 0, by norm_num⟩
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
  have h := variable_sound 12 ((3/4), (3243/640))
  have he : value ((3/4), (3243/640))=c := by norm_num [c,Data.centre,Data.coordinate,value]
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
  | 0 => ⟨((-55294967/33554432), (-47819087463/4294967296)), (3/8589934592), by norm_num⟩
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
  | 0 => ⟨((119377743703295/4503599627370496), (1716915035843083/9007199254740992)), (776289/4503599627370496), by norm_num⟩
  | 1 => ⟨((-8004751967/137438953472), (-115125973937/274877906944)), (107/274877906944), by norm_num⟩
  | 2 => ⟨((8794118879/137438953472), (7904925607/17179869184)), (61/137438953472), by norm_num⟩
  | 3 => ⟨((-12881769425/274877906944), (-23158529101/68719476736)), (23/68719476736), by norm_num⟩
  | 4 => ⟨((7076035095/274877906944), (101768978631/549755813888)), (13/68719476736), by norm_num⟩
  | 5 => ⟨((-12438110577/1099511627776), (-89443720423/1099511627776)), (47/549755813888), by norm_num⟩
  | 6 => ⟨((9109774085/2199023255552), (65509313601/2199023255552)), (71/2199023255552), by norm_num⟩
  | 7 => ⟨((-5718919861/4398046511104), (-82250670793/8796093022208)), (91/8796093022208), by norm_num⟩
  | 8 => ⟨((6282875637/17592186044416), (22590399421/8796093022208)), (103/35184372088832), by norm_num⟩
  | 9 => ⟨((-3067753059/35184372088832), (-88242099235/140737488355328)), (103/140737488355328), by norm_num⟩
  | 10 => ⟨((10784867869/562949953421312), (38777541839/281474976710656)), (93/562949953421312), by norm_num⟩
  | 11 => ⟨((-8617009725/2251799813685248), (-61965794893/2251799813685248)), (77/2251799813685248), by norm_num⟩
  | 12 => ⟨((6311168517/9007199254740992), (45384255831/9007199254740992)), (115/18014398509481984), by norm_num⟩
  | _ => zero

def term9ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790914584677707/5070602400912917605986812821504), (233268714891/1267650600228229401496703205376)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((889712248424245/316912650057057350374175801344), (1105023209677/316912650057057350374175801344)), (271/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((1890479322605591/39614081257132168796771975168), (2485937669893/39614081257132168796771975168)), (305/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1890300216607323/2475880078570760549798248448), (1320432168515/1237940039285380274899124224)), (81/309485009821345068724781056), by norm_num⟩
  | 14 => ⟨((885983080480033/77371252455336267181195264), (2640364436981/154742504910672534362390528)), (81/19342813113834066795298816), by norm_num⟩
  | 13 => ⟨((775140053865549/4835703278458516698824704), (2474810616335/9671406556917033397649408)), (19/302231454903657293676544), by norm_num⟩
  | 12 => ⟨((1259424206691871/604462909807314587353088), (2164928358949/604462909807314587353088)), (533/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((236103020343205/9444732965739290427392), (1758506664489/37778931862957161709568)), (865/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((1298313010220267/4722366482869645213696), (1318444694629/2361183241434822606848)), (649/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1622510891845181/590295810358705651712), (3624308623109/590295810358705651712)), (223/147573952589676412928), by norm_num⟩
  | 8 => ⟨((1824801794707673/73786976294838206464), (4528265135629/73786976294838206464)), (279/18446744073709551616), by norm_num⟩
  | 7 => ⟨((1824148173740169/9223372036854775808), (5091383672423/9223372036854775808)), (1255/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797697217517763/576460752303423488), (2543871167267/576460752303423488)), (157/144115188075855872), by norm_num⟩
  | 5 => ⟨((149476342875061/18014398509481984), (4447680674927/144115188075855872)), (275/36028797018963968), by norm_num⟩
  | 4 => ⟨((746738667563897/18014398509481984), (1665834967023/9007199254740992)), (413/9007199254740992), by norm_num⟩
  | 3 => ⟨((1491548802059499/9007199254740992), (8314872657311/9007199254740992)), (517/2251799813685248), by norm_num⟩
  | 2 => ⟨((2232504010313583/4503599627370496), (2073362256465/562949953421312)), (4143/4503599627370496), by norm_num⟩
  | 1 => ⟨((2222872100713837/2251799813685248), (12386718119575/1125899906842624)), (3119/1125899906842624), by norm_num⟩
  | 0 => ⟨((2194009143822225/2251799813685248), (12280118002779/562949953421312)), (12567/2251799813685248), by norm_num⟩
  | _ => zero

def term9ValueSquares : ℕ → Disk
  | 0 => ⟨((2194009143822225/2251799813685248), (12280118002779/562949953421312)), (47939309127043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((534157529586403/562949953421312), (95719667517759/2251799813685248)), (12519/1125899906842624), by norm_num⟩
  | 2 => ⟨((505820497473039/562949953421312), (181648051743785/2251799813685248)), (49645/2251799813685248), by norm_num⟩
  | 3 => ⟨((901650753153327/1125899906842624), (163213989697741/1125899906842624)), (97225/2251799813685248), by norm_num⟩
  | 4 => ⟨((1396812042438191/2251799813685248), (522824509858309/2251799813685248)), (91955/1125899906842624), by norm_num⟩
  | 5 => ⟨((186266381628971/562949953421312), (324312830569409/1125899906842624)), (78391/562949953421312), by norm_num⟩
  | 6 => ⟨((119377743703295/4503599627370496), (1716915035843083/9007199254740992)), (776289/4503599627370496), by norm_num⟩
  | _ => zero

def term9Value : CertifiedScalarExp.Data :=
  ⟨⟨((-55294967/33554432), (-47819087463/4294967296)), (3/8589934592), by norm_num⟩, -2, term9ValuePoly, term9ValueSquares⟩

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
  | 0 => ⟨((-7417145753/4294967296), (-100224181987/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((997232227621123/9007199254740992), (1253424236064659/9007199254740992)), (377581/4503599627370496), by norm_num⟩
  | 1 => ⟨((-17518707745/68719476736), (-44038634661/137438953472)), (7/34359738368), by norm_num⟩
  | 2 => ⟨((20169157651/68719476736), (50701351843/137438953472)), (17/68719476736), by norm_num⟩
  | 3 => ⟨((-30960801163/137438953472), (-38914725649/137438953472)), (7/34359738368), by norm_num⟩
  | 4 => ⟨((8911234903/68719476736), (11200558397/68719476736)), (35/274877906944), by norm_num⟩
  | 5 => ⟨((-8207550659/137438953472), (-41264382077/549755813888)), (17/274877906944), by norm_num⟩
  | 6 => ⟨((12599055865/549755813888), (63343167361/2199023255552)), (55/2199023255552), by norm_num⟩
  | 7 => ⟨((-33154740823/4398046511104), (-41672295117/4398046511104)), (19/2199023255552), by norm_num⟩
  | 8 => ⟨((19085402995/8796093022208), (47977002763/17592186044416)), (23/8796093022208), by norm_num⟩
  | 9 => ⟨((-39062901715/70368744177664), (-1534321269/2199023255552)), (49/70368744177664), by norm_num⟩
  | 10 => ⟨((35978262071/281474976710656), (5652648451/35184372088832)), (47/281474976710656), by norm_num⟩
  | 11 => ⟨((-60249461757/2251799813685248), (-18931933177/562949953421312)), (81/2251799813685248), by norm_num⟩
  | 12 => ⟨((23121585417/4503599627370496), (14530795705/2251799813685248)), (1/140737488355328), by norm_num⟩
  | _ => zero

def term10ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790863118239471/5070602400912917605986812821504), (146338684119/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889652093311393/316912650057057350374175801344), (346567195273/158456325028528675187087900672)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((1890344085517063/39614081257132168796771975168), (779657335545/19807040628566084398385987584)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((1890156668881085/2475880078570760549798248448), (1656479888643/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885911386270237/77371252455336267181195264), (828075765975/77371252455336267181195264)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1550145850275055/9671406556917033397649408), (1552293266121/9671406556917033397649408)), (203/4835703278458516698824704), by norm_num⟩
  | 12 => ⟨((1259306900519677/604462909807314587353088), (678953953581/302231454903657293676544)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944316928550103/37778931862957161709568), (137871670991/4722366482869645213696)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((20283914969977/73786976294838206464), (826944170363/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1622315470085197/590295810358705651712), (2273167813573/590295810358705651712)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1824558191815157/73786976294838206464), (355008430227/9223372036854775808)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823875046692775/9223372036854775808), (199572655779/576460752303423488)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((3115473563083/2251799813685248), (797693092089/288230376151711744)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((149446758433195/18014398509481984), (2789239131751/144115188075855872)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1493124914577821/36028797018963968), (2089245404915/18014398509481984)), (549/18014398509481984), by norm_num⟩
  | 3 => ⟨((745556401263371/4503599627370496), (162929126773/281474976710656)), (687/4503599627370496), by norm_num⟩
  | 2 => ⟨((278955693142331/562949953421312), (2599842269947/1125899906842624)), (2751/4503599627370496), by norm_num⟩
  | 1 => ⟨((2221618082005567/2251799813685248), (15528988433847/2251799813685248)), (517/281474976710656), by norm_num⟩
  | 0 => ⟨((1095817445632901/1125899906842624), (7694687095243/562949953421312)), (8309/2251799813685248), by norm_num⟩
  | _ => zero

def term10ValueSquares : ℕ → Disk
  | 0 => ⟨((1095817445632901/1125899906842624), (7694687095243/562949953421312)), (31696328170012717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((16661381181885/17592186044416), (936136985447/35184372088832)), (8201/1125899906842624), by norm_num⟩
  | 2 => ⟨((2018223565931775/2251799813685248), (443302927607/8796093022208)), (15971/1125899906842624), by norm_num⟩
  | 3 => ⟨((1803156465094193/2251799813685248), (50856920969579/562949953421312)), (30239/1125899906842624), by norm_num⟩
  | 4 => ⟨((1425522107042671/2251799813685248), (40724306523057/281474976710656)), (53893/1125899906842624), by norm_num⟩
  | 5 => ⟨((213825762939513/562949953421312), (206247105590051/1125899906842624)), (41915/562949953421312), by norm_num⟩
  | 6 => ⟨((997232227621123/9007199254740992), (1253424236064659/9007199254740992)), (377581/4503599627370496), by norm_num⟩
  | _ => zero

def term10Value : CertifiedScalarExp.Data :=
  ⟨⟨((-7417145753/4294967296), (-100224181987/8589934592)), (1/4294967296), by norm_num⟩, -2, term10ValuePoly, term10ValueSquares⟩

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
  | 0 => ⟨((-1931040333/1073741824), (-104372729997/8589934592)), (3/8589934592), by norm_num⟩
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
  | 0 => ⟨((1364178072013001/9007199254740992), (602321752500357/9007199254740992)), (770953/9007199254740992), by norm_num⟩
  | 1 => ⟨((-49913881685/137438953472), (-2754792181/17179869184)), (15/68719476736), by norm_num⟩
  | 2 => ⟨((29922065235/68719476736), (26422812593/137438953472)), (19/68719476736), by norm_num⟩
  | 3 => ⟨((-23916659593/68719476736), (-10559856235/68719476736)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((57349644979/274877906944), (25321429347/274877906944)), (5/34359738368), by norm_num⟩
  | 5 => ⟨((-55007377037/549755813888), (-24287254293/549755813888)), (41/549755813888), by norm_num⟩
  | 6 => ⟨((87934619577/2199023255552), (9706382043/549755813888)), (17/549755813888), by norm_num⟩
  | 7 => ⟨((-30122572657/2199023255552), (-13299935781/2199023255552)), (3/274877906944), by norm_num⟩
  | 8 => ⟨((72230774579/17592186044416), (15945926569/8796093022208)), (15/4398046511104), by norm_num⟩
  | 9 => ⟨((-38489296203/35184372088832), (-33988143947/70368744177664)), (33/35184372088832), by norm_num⟩
  | 10 => ⟨((73834641135/281474976710656), (32600003881/281474976710656)), (33/140737488355328), by norm_num⟩
  | 11 => ⟨((-64380995253/1125899906842624), (-28425961891/1125899906842624)), (15/281474976710656), by norm_num⟩
  | 12 => ⟨((25729814029/2251799813685248), (5680206637/1125899906842624)), (25/2251799813685248), by norm_num⟩
  | _ => zero

def term11ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790816561182973/5070602400912917605986812821504), (67700905901/1267650600228229401496703205376)), (57/1267650600228229401496703205376), by norm_num⟩
  | 17 => ⟨((1779194741769803/633825300114114700748351602688), (641256187909/633825300114114700748351602688)), (541/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472555256424883/9903520314283042199192993792), (721299232711/39614081257132168796771975168)), (609/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((945013000480725/1237940039285380274899124224), (47889990241/154742504910672534362390528)), (647/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771692198097631/154742504910672534362390528), (191520431997/38685626227668133590597632)), (647/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((775011768004597/4835703278458516698824704), (718033667267/9671406556917033397649408)), (607/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629599987380477/302231454903657293676544), (157027889301/151115727451828646838272)), (531/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((944230144340027/37778931862957161709568), (1020366573335/75557863725914323419136)), (431/37778931862957161709568), by norm_num⟩
  | 10 => ⟨((649020272175987/2361183241434822606848), (764999669707/4722366482869645213696)), (647/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((811068482608555/295147905179352825856), (131428431387/73786976294838206464)), (445/295147905179352825856), by norm_num⟩
  | 8 => ⟨((57010483012135/2305843009213693952), (656807013605/36893488147419103232)), (139/9223372036854775808), by norm_num⟩
  | 7 => ⟨((1823625012798413/9223372036854775808), (369223678435/2305843009213693952)), (1251/9223372036854775808), by norm_num⟩
  | 6 => ⟨((199359138609627/144115188075855872), (737872122741/576460752303423488)), (1251/1152921504606846976), by norm_num⟩
  | 5 => ⟨((145917559031/17592186044416), (1289983126861/144115188075855872)), (137/18014398509481984), by norm_num⟩
  | 4 => ⟨((1492800300047105/36028797018963968), (1932391483635/36028797018963968)), (1643/36028797018963968), by norm_num⟩
  | 3 => ⟨((1490709690056831/9007199254740992), (2410975415591/9007199254740992)), (1027/4503599627370496), by norm_num⟩
  | 2 => ⟨((69713976907593/140737488355328), (4808435665015/4503599627370496)), (4111/4503599627370496), by norm_num⟩
  | 1 => ⟨((1110220208190921/1125899906842624), (7178958679299/2251799813685248)), (1543/562949953421312), by norm_num⟩
  | 0 => ⟨((2189358054441453/2251799813685248), (14223695229813/2251799813685248)), (6185/1125899906842624), by norm_num⟩
  | _ => zero

def term11ValueSquares : ℕ → Disk
  | 0 => ⟨((2189358054441453/2251799813685248), (14223695229813/2251799813685248)), (23593906882857921/4294967296000000000000000000), by norm_num⟩
  | 1 => ⟨((133034871370221/140737488355328), (6914638132141/562949953421312)), (24211/2251799813685248), by norm_num⟩
  | 2 => ⟨((502930354761875/562949953421312), (3268098660957/140737488355328)), (1449/70368744177664), by norm_num⟩
  | 3 => ⟨((898012523859327/1125899906842624), (46714661122903/1125899906842624)), (85003/2251799813685248), by norm_num⟩
  | 4 => ⟨((89289046539195/140737488355328), (149037584891017/2251799813685248)), (142651/2251799813685248), by norm_num⟩
  | 5 => ⟨((1793015921736757/4503599627370496), (378219734029223/4503599627370496)), (399779/4503599627370496), by norm_num⟩
  | 6 => ⟨((1364178072013001/9007199254740992), (602321752500357/9007199254740992)), (770953/9007199254740992), by norm_num⟩
  | _ => zero

def term11Value : CertifiedScalarExp.Data :=
  ⟨⟨((-1931040333/1073741824), (-104372729997/8589934592)), (3/8589934592), by norm_num⟩, -2, term11ValuePoly, term11ValueSquares⟩

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
  | 0 => ⟨((-2001111149/1073741824), (-54080028801/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((1396583245649873/9007199254740992), (-274107650259/70368744177664)), (343451/9007199254740992), by norm_num⟩
  | 1 => ⟨((-26476890519/68719476736), (1330335787/137438953472)), (7/68719476736), by norm_num⟩
  | 2 => ⟨((131585202633/274877906944), (-826440061/68719476736)), (19/137438953472), by norm_num⟩
  | 3 => ⟨((-108992315013/274877906944), (1369084269/137438953472)), (17/137438953472), by norm_num⟩
  | 4 => ⟨((8463616511/34359738368), (-850511651/137438953472)), (23/274877906944), by norm_num⟩
  | 5 => ⟨((-67300150239/549755813888), (845376823/274877906944)), (25/549755813888), by norm_num⟩
  | 6 => ⟨((111489727241/2199023255552), (-2800909985/2199023255552)), (11/549755813888), by norm_num⟩
  | 7 => ⟨((-9894341593/549755813888), (1988571385/4398046511104)), (33/4398046511104), by norm_num⟩
  | 8 => ⟨((98346060879/17592186044416), (-2470707129/17592186044416)), (43/17592186044416), by norm_num⟩
  | 9 => ⟨((-108613680293/70368744177664), (2728656255/70368744177664)), (25/35184372088832), by norm_num⟩
  | 10 => ⟨((13494742821/35184372088832), (-2712182429/281474976710656)), (13/70368744177664), by norm_num⟩
  | 11 => ⟨((-48775528979/562949953421312), (2450734601/1125899906842624)), (49/1125899906842624), by norm_num⟩
  | 12 => ⟨((40400878769/2251799813685248), (-1014974451/2251799813685248)), (43/4503599627370496), by norm_num⟩
  | _ => zero

def term12ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((790774057920435/5070602400912917605986812821504), (-8179521967/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1779094319639689/633825300114114700748351602688), (-38733635505/633825300114114700748351602688)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((945054040764127/19807040628566084398385987584), (-10892055421/9903520314283042199192993792)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889906036364399/2475880078570760549798248448), (-46282436393/2475880078570760549798248448)), (431/2475880078570760549798248448), by norm_num⟩
  | 14 => ⟨((1771572276887635/154742504910672534362390528), (-46272540635/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774955577977723/4835703278458516698824704), (-21684997799/4835703278458516698824704)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1259101688274153/604462909807314587353088), (-592784973/9444732965739290427392)), (177/302231454903657293676544), by norm_num⟩
  | 11 => ⟨((1888300659458617/75557863725914323419136), (-30814971043/37778931862957161709568)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648960448961133/2361183241434822606848), (-46205230505/4722366482869645213696)), (431/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((1621972573960487/590295810358705651712), (-15876053253/147573952589676412928)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((912065075526005/36893488147419103232), (-79338321331/73786976294838206464)), (741/73786976294838206464), by norm_num⟩
  | 7 => ⟨((1823394296699603/9223372036854775808), (-89197975315/9223372036854775808)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((1594642707938667/1152921504606846976), (-89125987201/1152921504606846976)), (833/1152921504606846976), by norm_num⟩
  | 5 => ⟨((37348606151321/4503599627370496), (-77904330633/144115188075855872)), (729/144115188075855872), by norm_num⟩
  | 4 => ⟨((746249568458269/18014398509481984), (-116694875559/36028797018963968)), (547/18014398509481984), by norm_num⟩
  | 3 => ⟨((186291808837193/1125899906842624), (-145586199071/9007199254740992)), (683/4503599627370496), by norm_num⟩
  | 2 => ⟨((2230100515370627/4503599627370496), (-290326970387/4503599627370496)), (683/1125899906842624), by norm_num⟩
  | 1 => ⟨((2219329493430809/2251799813685248), (-433383027739/2251799813685248)), (2049/1125899906842624), by norm_num⟩
  | 0 => ⟨((2187172769189665/2251799813685248), (-429186545687/1125899906842624)), (8197/2251799813685248), by norm_num⟩
  | _ => zero

def term12ValueSquares : ℕ → Disk
  | 0 => ⟨((2187172769189665/2251799813685248), (-429186545687/1125899906842624)), (31269082076262717/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1062200102426397/1125899906842624), (-1667475270091/2251799813685248)), (15931/2251799813685248), by norm_num⟩
  | 2 => ⟨((1002103611181763/1125899906842624), (-1573134869201/1125899906842624)), (7521/562949953421312), by norm_num⟩
  | 3 => ⟨((1783833832274363/2251799813685248), (-700081829531/281474976710656)), (53637/2251799813685248), by norm_num⟩
  | 4 => ⟨((1413105976159861/2251799813685248), (-4436734190271/1125899906842624)), (333/8796093022208), by norm_num⟩
  | 5 => ⟨((886752787384643/2251799813685248), (-22274006990503/4503599627370496)), (215333/4503599627370496), by norm_num⟩
  | 6 => ⟨((1396583245649873/9007199254740992), (-274107650259/70368744177664)), (343451/9007199254740992), by norm_num⟩
  | _ => zero

def term12Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2001111149/1073741824), (-54080028801/4294967296)), (1/4294967296), by norm_num⟩, -2, term12ValuePoly, term12ValueSquares⟩

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
  | 0 => ⟨((-16524560409/8589934592), (-55822030633/4294967296)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((149433682181217/1125899906842624), (-549293200928091/9007199254740992)), (229775/4503599627370496), by norm_num⟩
  | 1 => ⟨((-93576617943/274877906944), (1343640559/8589934592)), (39/274877906944), by norm_num⟩
  | 2 => ⟨((60004821517/137438953472), (-6892739977/34359738368)), (27/137438953472), by norm_num⟩
  | 3 => ⟨((-51303109465/137438953472), (5893176325/34359738368)), (25/137438953472), by norm_num⟩
  | 4 => ⟨((65794938829/274877906944), (-30231397657/274877906944)), (17/137438953472), by norm_num⟩
  | 5 => ⟨((-33752137215/274877906944), (15508400799/274877906944)), (37/549755813888), by norm_num⟩
  | 6 => ⟨((57715015109/1099511627776), (-26518841777/1099511627776)), (17/549755813888), by norm_num⟩
  | 7 => ⟨((-84592051955/4398046511104), (38868277815/4398046511104)), (53/4398046511104), by norm_num⟩
  | 8 => ⟨((54243582327/8796093022208), (-6230947763/2199023255552)), (9/2199023255552), by norm_num⟩
  | 9 => ⟨((-30918231475/17592186044416), (7103140205/8796093022208)), (43/35184372088832), by norm_num⟩
  | 10 => ⟨((63442958365/140737488355328), (-3643838981/17592186044416)), (23/70368744177664), by norm_num⟩
  | 11 => ⟨((-29586904599/281474976710656), (849660223/17592186044416)), (45/562949953421312), by norm_num⟩
  | 12 => ⟨((50592607961/2251799813685248), (-11623122363/1125899906842624)), (5/281474976710656), by norm_num⟩
  | _ => zero

def term13ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581469917418293/10141204801825835211973625643008), (-70130772629/1267650600228229401496703205376)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((889500756529093/316912650057057350374175801344), (-83016793649/79228162514264337593543950336)), (361/633825300114114700748351602688), by norm_num⟩
  | 16 => ⟨((472500919506279/9903520314283042199192993792), (-747025234345/39614081257132168796771975168)), (203/19807040628566084398385987584), by norm_num⟩
  | 15 => ⟨((1889795111715933/2475880078570760549798248448), (-793558575033/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((1771461356828861/154742504910672534362390528), (-793383430431/154742504910672534362390528)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((774903586640835/4835703278458516698824704), (-743610928721/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((157376338540163/75557863725914323419136), (-650473585893/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888152826209227/75557863725914323419136), (-1056670999355/75557863725914323419136)), (575/75557863725914323419136), by norm_num⟩
  | 10 => ⟨((648905015511937/2361183241434822606848), (-396099186309/2361183241434822606848)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((1621820145059371/590295810358705651712), (-1088777578411/590295810358705651712)), (593/590295810358705651712), by norm_num⟩
  | 8 => ⟨((911969817294609/36893488147419103232), (-1360229618663/73786976294838206464)), (371/36893488147419103232), by norm_num⟩
  | 7 => ⟨((911589996388505/4611686018427387904), (-1529238268355/9223372036854775808)), (417/4611686018427387904), by norm_num⟩
  | 6 => ⟨((398607109494841/288230376151711744), (-1527964228679/1152921504606846976)), (835/1152921504606846976), by norm_num⟩
  | 5 => ⟨((1194967948961077/144115188075855872), (-333884203785/36028797018963968)), (731/144115188075855872), by norm_num⟩
  | 4 => ⟨((1492218042071603/36028797018963968), (-2000444973291/36028797018963968)), (137/4503599627370496), by norm_num⟩
  | 3 => ⟨((186247904693413/1125899906842624), (-2495558691019/9007199254740992)), (685/4503599627370496), by norm_num⟩
  | 2 => ⟨((2229398458063055/4503599627370496), (-622019549729/562949953421312)), (2741/4503599627370496), by norm_num⟩
  | 1 => ⟨((2218277439617135/2251799813685248), (-7426942481227/2251799813685248)), (4115/2251799813685248), by norm_num⟩
  | 0 => ⟨((1092536423883339/1125899906842624), (-14705376741693/2251799813685248)), (8249/2251799813685248), by norm_num⟩
  | _ => zero

def term13ValueSquares : ℕ → Disk
  | 0 => ⟨((1092536423883339/1125899906842624), (-14705376741693/2251799813685248)), (31467446334075217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2120227150267191/2251799813685248), (-1783702043537/140737488355328)), (8059/1125899906842624), by norm_num⟩
  | 2 => ⟨((498995143086403/562949953421312), (-419870083223/17592186044416)), (15381/1125899906842624), by norm_num⟩
  | 3 => ⟨((883970695595875/1125899906842624), (-47637770934571/1125899906842624)), (14001/562949953421312), by norm_num⟩
  | 4 => ⟨((1384021490218573/2251799813685248), (-149606171041475/2251799813685248)), (11585/281474976710656), by norm_num⟩
  | 5 => ⟨((1681440301635771/4503599627370496), (-367809171192443/4503599627370496)), (126243/2251799813685248), by norm_num⟩
  | 6 => ⟨((149433682181217/1125899906842624), (-549293200928091/9007199254740992)), (229775/4503599627370496), by norm_num⟩
  | _ => zero

def term13Value : CertifiedScalarExp.Data :=
  ⟨⟨((-16524560409/8589934592), (-55822030633/4294967296)), (1/4294967296), by norm_num⟩, -2, term13ValuePoly, term13ValueSquares⟩

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
  | 0 => ⟨((-2125249673/1073741824), (-114869744829/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((13460510163767/140737488355328), (-449064824613505/4503599627370496)), (139743/2251799813685248), by norm_num⟩
  | 1 => ⟨((-542038849/2147483648), (9041655097/34359738368)), (3/17179869184), by norm_num⟩
  | 2 => ⟨((45775091117/137438953472), (-47722892311/137438953472)), (17/68719476736), by norm_num⟩
  | 3 => ⟨((-40267696575/137438953472), (41981149581/137438953472)), (1/4294967296), by norm_num⟩
  | 4 => ⟨((53134379897/274877906944), (-27697665127/137438953472)), (11/68719476736), by norm_num⟩
  | 5 => ⟨((-56089869889/549755813888), (58476580933/549755813888)), (49/549755813888), by norm_num⟩
  | 6 => ⟨((49341460749/1099511627776), (-12860254127/274877906944)), (23/549755813888), by norm_num⟩
  | 7 => ⟨((-37204269613/2199023255552), (38787369045/2199023255552)), (37/2199023255552), by norm_num⟩
  | 8 => ⟨((3068256263/549755813888), (-6397630661/1099511627776)), (51/8796093022208), by norm_num⟩
  | 9 => ⟨((-57580829725/35184372088832), (234496029/137438953472)), (31/17592186044416), by norm_num⟩
  | 10 => ⟨((60783644293/140737488355328), (-15842520681/35184372088832)), (17/35184372088832), by norm_num⟩
  | 11 => ⟨((-58331462543/562949953421312), (60813556833/562949953421312)), (17/140737488355328), by norm_num⟩
  | 12 => ⟨((12828339481/562949953421312), (-53496820967/2251799813685248)), (31/1125899906842624), by norm_num⟩
  | _ => zero

def term14ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581397516987371/10141204801825835211973625643008), (-262550398137/2535301200456458802993406410752)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((444728805657395/158456325028528675187087900672), (-621527257433/316912650057057350374175801344)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((944953292143221/19807040628566084398385987584), (-1398193706969/39614081257132168796771975168)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((472422981642317/618970019642690137449562112), (-742640429705/1237940039285380274899124224)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((885679072891509/77371252455336267181195264), (-742471760765/77371252455336267181195264)), (433/154742504910672534362390528), by norm_num⟩
  | 13 => ⟨((1549710385432853/9671406556917033397649408), (-1391776232469/9671406556917033397649408)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((629462995743935/302231454903657293676544), (-1217445999803/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1888015109915331/75557863725914323419136), (-1977678362963/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((648853349426223/2361183241434822606848), (-1482671553795/4722366482869645213696)), (27/295147905179352825856), by norm_num⟩
  | 9 => ⟨((405419497597021/147573952589676412928), (-1018859807797/295147905179352825856)), (297/295147905179352825856), by norm_num⟩
  | 8 => ⟨((1823761832038737/73786976294838206464), (-2545719666139/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((911489907526859/4611686018427387904), (-2861969880069/9223372036854775808)), (209/2305843009213693952), by norm_num⟩
  | 6 => ⟨((797114036702717/576460752303423488), (-357439488039/144115188075855872)), (209/288230376151711744), by norm_num⟩
  | 5 => ⟨((298698105098223/36028797018963968), (-2499318378989/144115188075855872)), (183/36028797018963968), by norm_num⟩
  | 4 => ⟨((1491954331686861/36028797018963968), (-1871734100429/18014398509481984)), (549/18014398509481984), by norm_num⟩
  | 3 => ⟨((744826436237779/4503599627370496), (-4669708930045/9007199254740992)), (687/4503599627370496), by norm_num⟩
  | 2 => ⟨((2228735560971419/4503599627370496), (-4655299547423/2251799813685248)), (2749/4503599627370496), by norm_num⟩
  | 1 => ⟨((1108638863283147/1125899906842624), (-868378875673/140737488355328)), (1033/562949953421312), by norm_num⟩
  | 0 => ⟨((2183052250332413/2251799813685248), (-6875508976049/562949953421312)), (8297/2251799813685248), by norm_num⟩
  | _ => zero

def term14ValueSquares : ℕ → Disk
  | 0 => ⟨((2183052250332413/2251799813685248), (-6875508976049/562949953421312)), (31650551802825217/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((2116067661407389/2251799813685248), (-6665599335751/281474976710656)), (16291/2251799813685248), by norm_num⟩
  | 2 => ⟨((1987254278435305/2251799813685248), (-50110526211289/1125899906842624)), (15695/1125899906842624), by norm_num⟩
  | 3 => ⟨((1749327486338153/2251799813685248), (-176893802020623/2251799813685248)), (58199/2251799813685248), by norm_num⟩
  | 4 => ⟨((1345081929067171/2251799813685248), (-274842539871343/2251799813685248)), (99569/2251799813685248), by norm_num⟩
  | 5 => ⟨((1539841120550395/4503599627370496), (-656693781521985/4503599627370496)), (286517/4503599627370496), by norm_num⟩
  | 6 => ⟨((13460510163767/140737488355328), (-449064824613505/4503599627370496)), (139743/2251799813685248), by norm_num⟩
  | _ => zero

def term14Value : CertifiedScalarExp.Data :=
  ⟨⟨((-2125249673/1073741824), (-114869744829/8589934592)), (1/4294967296), by norm_num⟩, -2, term14ValuePoly, term14ValueSquares⟩

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
  | 0 => ⟨((-8723240287/4294967296), (-117872784381/8589934592)), (1/4294967296), by norm_num⟩
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
  | 0 => ⟨((238215636067241/4503599627370496), (-540721450326877/4503599627370496)), (636151/9007199254740992), by norm_num⟩
  | 1 => ⟨((-2460860829/17179869184), (5585864381/17179869184)), (55/274877906944), by norm_num⟩
  | 2 => ⟨((26656538651/137438953472), (-60507204641/137438953472)), (39/137438953472), by norm_num⟩
  | 3 => ⟨((-24062414951/137438953472), (3413678077/8589934592)), (37/137438953472), by norm_num⟩
  | 4 => ⟨((32581113823/274877906944), (-73955292823/274877906944)), (13/68719476736), by norm_num⟩
  | 5 => ⟨((-275722787/4294967296), (80109858241/549755813888)), (59/549755813888), by norm_num⟩
  | 6 => ⟨((31857969015/1099511627776), (-9039229905/137438953472)), (55/1099511627776), by norm_num⟩
  | 7 => ⟨((-24649422685/2199023255552), (55951287685/2199023255552)), (11/549755813888), by norm_num⟩
  | 8 => ⟨((33375937029/8796093022208), (-75759447933/8796093022208)), (31/4398046511104), by norm_num⟩
  | 9 => ⟨((-1255329347/1099511627776), (11397799345/4398046511104)), (77/35184372088832), by norm_num⟩
  | 10 => ⟨((5439191825/17592186044416), (-49385300493/70368744177664)), (43/70368744177664), by norm_num⟩
  | 11 => ⟨((-21424879295/281474976710656), (48631953793/281474976710656)), (11/70368744177664), by norm_num⟩
  | 12 => ⟨((38679765789/2251799813685248), (-5487407177/140737488355328)), (41/1125899906842624), by norm_num⟩
  | _ => zero

def term15ValuePoly : ℕ → Disk
  | 20 => ⟨(0, 0), 0, by norm_num⟩
  | 19 => ⟨((666937165097003/81129638414606681695789005144064), 0), (1/162259276829213363391578010288128), by norm_num⟩
  | 18 => ⟨((1581330113798723/10141204801825835211973625643008), (-1505594385787/10141204801825835211973625643008)), (19/633825300114114700748351602688), by norm_num⟩
  | 17 => ⟨((1778834572752503/633825300114114700748351602688), (-1781920835301/633825300114114700748351602688)), (181/316912650057057350374175801344), by norm_num⟩
  | 16 => ⟨((118113488729987/2475880078570760549798248448), (-501075877373/9903520314283042199192993792)), (407/39614081257132168796771975168), by norm_num⟩
  | 15 => ⟨((944797722277859/1237940039285380274899124224), (-2129131157101/2475880078570760549798248448)), (27/154742504910672534362390528), by norm_num⟩
  | 14 => ⟨((442815403406357/38685626227668133590597632), (-266079352977/19342813113834066795298816)), (27/9671406556917033397649408), by norm_num⟩
  | 13 => ⟨((1549619833298745/9671406556917033397649408), (-997533969743/4835703278458516698824704)), (405/9671406556917033397649408), by norm_num⟩
  | 12 => ⟨((1258846705181067/604462909807314587353088), (-1745157403763/604462909807314587353088)), (355/604462909807314587353088), by norm_num⟩
  | 11 => ⟨((1887886170036163/75557863725914323419136), (-2834892924517/75557863725914323419136)), (9/1180591620717411303424), by norm_num⟩
  | 10 => ⟨((1297609906865833/4722366482869645213696), (-2125305668307/4722366482869645213696)), (433/4722366482869645213696), by norm_num⟩
  | 9 => ⟨((810772380046245/295147905179352825856), (-1460445954055/295147905179352825856)), (595/590295810358705651712), by norm_num⟩
  | 8 => ⟨((1823595082524339/73786976294838206464), (-3649010952041/73786976294838206464)), (743/73786976294838206464), by norm_num⟩
  | 7 => ⟨((113924495710477/576460752303423488), (-1025561568423/2305843009213693952)), (837/9223372036854775808), by norm_num⟩
  | 6 => ⟨((797019913704717/576460752303423488), (-4098635253755/1152921504606846976)), (837/1152921504606846976), by norm_num⟩
  | 5 => ⟨((597313649318321/72057594037927936), (-1791123641017/72057594037927936)), (733/144115188075855872), by norm_num⟩
  | 4 => ⟨((1491705838750561/36028797018963968), (-2682631682863/18014398509481984)), (275/9007199254740992), by norm_num⟩
  | 3 => ⟨((1489340844378473/9007199254740992), (-6692412497297/9007199254740992)), (43/281474976710656), by norm_num⟩
  | 2 => ⟨((2228107293339459/4503599627370496), (-13342410811625/4503599627370496)), (689/1125899906842624), by norm_num⟩
  | 1 => ⟨((138520305089583/140737488355328), (-9953940527567/1125899906842624)), (4147/2251799813685248), by norm_num⟩
  | 0 => ⟨((34079770194985/35184372088832), (-39394619092739/2251799813685248)), (8343/2251799813685248), by norm_num⟩
  | _ => zero

def term15ValueSquares : ℕ → Disk
  | 0 => ⟨((34079770194985/35184372088832), (-39394619092739/2251799813685248)), (31826027877043967/8589934592000000000000000000), by norm_num⟩
  | 1 => ⟨((1055970502343099/1125899906842624), (-38157837866479/1125899906842624)), (16455/2251799813685248), by norm_num⟩
  | 2 => ⟨((989091192263285/1125899906842624), (-71575725293713/1125899906842624)), (15991/1125899906842624), by norm_num⟩
  | 3 => ⟨((864355966500239/1125899906842624), (-125757039391537/1125899906842624)), (60259/2251799813685248), by norm_num⟩
  | 4 => ⟨((1299043368639797/2251799813685248), (-96543970442547/562949953421312)), (105985/2251799813685248), by norm_num⟩
  | 5 => ⟨((683178785519289/2251799813685248), (-445562891775165/2251799813685248)), (158637/2251799813685248), by norm_num⟩
  | 6 => ⟨((238215636067241/4503599627370496), (-540721450326877/4503599627370496)), (636151/9007199254740992), by norm_num⟩
  | _ => zero

def term15Value : CertifiedScalarExp.Data :=
  ⟨⟨((-8723240287/4294967296), (-117872784381/8589934592)), (1/4294967296), by norm_num⟩, -2, term15ValuePoly, term15ValueSquares⟩

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
theorem term9Jet_sound : Sound term9Jet F_term9 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term9

def term10Jet : Jet 12 := J_term10
theorem term10Jet_sound : Sound term10Jet F_term10 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term10

def term11Jet : Jet 12 := J_term11
theorem term11Jet_sound : Sound term11Jet F_term11 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term11

def term12Jet : Jet 12 := J_term12
theorem term12Jet_sound : Sound term12Jet F_term12 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term12

def term13Jet : Jet 12 := J_term13
theorem term13Jet_sound : Sound term13Jet F_term13 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term13

def term14Jet : Jet 12 := J_term14
theorem term14Jet_sound : Sound term14Jet F_term14 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term14

def term15Jet : Jet 12 := J_term15
theorem term15Jet_sound : Sound term15Jet F_term15 (Data.centre ⟨11,by norm_num [Data.count]⟩) := S_term15

end Reinmann.XiRectangle.Tile011Terms1
